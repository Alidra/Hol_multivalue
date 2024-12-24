Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SUP_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SUP_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367765_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19158_spec.
Require Import thm19490_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981223_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982725_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1982796_spec.
Require Import thm1982797_spec.
Require Import thm1988285_spec.
Require Import thm1988287_spec.
Require Import thm1988295_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5323607 (x : real) : term0 x.
Proof. exact (@lem1495933 x). Qed.
Lemma lem5323608 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem5323609 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem5323608 x) (@lem5323607 x)). Qed.
Lemma lem5323610 (x : real) (y : real) : term2 x y.
Proof. exact (@lem5323609 x y). Qed.
Lemma lem5323611 (y : real) (x : real) : (term2 x y) = ((term3 x y) = (real_lt y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem5323613 (s : real -> Prop) : term4 s.
Proof. exact (@lem5319392 s). Qed.
Lemma lem5323614 (s : real -> Prop) : (term4 s) = (term5 s).
Proof. exact (eq_refl (term4 s)). Qed.
Lemma lem5323615 (s : real -> Prop) : term5 s.
Proof. exact (EQ_MP (@lem5323614 s) (@lem5323613 s)). Qed.
Lemma lem5323616 (s : real -> Prop) (l : real) : term6 s l.
Proof. exact (@lem5323615 s l). Qed.
Lemma lem5323617 (l : real) (s : real -> Prop) : (term6 s l) = ((has_sup s l) = (term7 l s)).
Proof. exact (eq_refl (term6 s l)). Qed.
Lemma lem5323619 (s : real -> Prop) : term4 s.
Proof. exact (@lem5319392 s). Qed.
Lemma lem5323620 (s : real -> Prop) : (term4 s) = (term5 s).
Proof. exact (eq_refl (term4 s)). Qed.
Lemma lem5323621 (s : real -> Prop) : term5 s.
Proof. exact (EQ_MP (@lem5323620 s) (@lem5323619 s)). Qed.
Lemma lem5323622 (s : real -> Prop) (l : real) : term6 s l.
Proof. exact (@lem5323621 s l). Qed.
Lemma lem5323623 (l : real) (s : real -> Prop) : (term6 s l) = ((has_sup s l) = (term7 l s)).
Proof. exact (eq_refl (term6 s l)). Qed.
Lemma lem5323633 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : term8 l m t s.
Proof. exact (h1). Qed.
Lemma lem5323634 (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term9 m t s) : term9 m t s.
Proof. exact (h1). Qed.
Lemma lem5323635 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5323636 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term10 t s.
Proof. exact (h1). Qed.
Lemma lem5323637 (t : real -> Prop) (m : real) (h1 : has_sup t m) : has_sup t m.
Proof. exact (h1). Qed.
Lemma lem5323639 (l : real) (s : real -> Prop) : (has_sup s l) = (term7 l s).
Proof. exact (EQ_MP (@lem5323623 l s) (@lem5323622 s l)). Qed.
Lemma lem5323664 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term7 l s.
Proof. exact (EQ_MP (@lem5323639 l s) (@lem5323635 s l h1)). Qed.
Lemma lem5323665 (l : real) (s : real -> Prop) (h1 : term11 l s) : term11 l s.
Proof. exact (h1). Qed.
Lemma lem5323666 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5323668 (s : real -> Prop) (l : real) (h1 : term13 s l) : term13 s l.
Proof. exact (h1). Qed.
Lemma lem5323670 (l : real) (s : real -> Prop) : (has_sup s l) = (term7 l s).
Proof. exact (EQ_MP (@lem5323617 l s) (@lem5323616 s l)). Qed.
Lemma lem5323671 (m : real) (t : real -> Prop) : (has_sup t m) = (term7 m t).
Proof. exact (@lem5323670 m t). Qed.
Lemma lem5323696 (t : real -> Prop) (m : real) (h1 : has_sup t m) : term7 m t.
Proof. exact (EQ_MP (@lem5323671 m t) (@lem5323637 t m h1)). Qed.
Lemma lem5323697 (m : real) (t : real -> Prop) (h1 : term11 m t) : term11 m t.
Proof. exact (h1). Qed.
Lemma lem5323698 (t : real -> Prop) (h1 : term12 t) : term12 t.
Proof. exact (h1). Qed.
Lemma lem5323699 (m : real) (t : real -> Prop) (h1 : term14 m t) : term14 m t.
Proof. exact (h1). Qed.
Lemma lem5323702 (p : Prop) : p = (term15 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5323703 (m : real) (l : real) : (real_le m l) = (term16 m l).
Proof. exact (@lem5323702 (real_le m l)). Qed.
Lemma lem5323704 (m : real) (l : real) : (term16 m l) = (real_le m l).
Proof. exact (SYM (@lem5323703 m l)). Qed.
Lemma lem5323705 (m : real) (l : real) (h1 : term3 m l) : term3 m l.
Proof. exact (h1). Qed.
Lemma lem5323707 (y : real) (x : real) : (term3 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem5323611 y x) (@lem5323610 x y)). Qed.
Lemma lem5323708 (l : real) (m : real) : (term3 m l) = (real_lt l m).
Proof. exact (@lem5323707 l m). Qed.
Lemma lem5323709 (m : real) (l : real) (h1 : term3 m l) : real_lt l m.
Proof. exact (EQ_MP (@lem5323708 l m) (@lem5323705 m l h1)). Qed.
Lemma lem5323710 (l : real) (m : real) (h1 : term17 l m) : term17 l m.
Proof. exact (h1). Qed.
Lemma lem5323711 (l : real) (c : real) (m : real) (h1 : term18 l c m) : term18 l c m.
Proof. exact (h1). Qed.
Lemma lem5323712 (c : real) (m : real) (h1 : real_lt c m) : real_lt c m.
Proof. exact (h1). Qed.
Lemma lem5323713 (l : real) (c : real) (h1 : real_lt l c) : real_lt l c.
Proof. exact (h1). Qed.
Lemma lem5323735 (l : real) (m : real) : (term19 l m) = (term20 l m).
Proof. exact (@lem17045 (term21 l m) (term22 l m)). Qed.
Lemma lem5323737 (l : real) (m : real) : (term23 l m) = (term23 l m).
Proof. exact (eq_refl (term23 l m)). Qed.
Lemma lem5323738 (l : real) (m : real) : (term24 l m) = (term25 l m).
Proof. exact (MK_COMB (@lem5323737 l m) (@lem5323735 l m)). Qed.
Lemma lem5323739 (l : real) (m : real) : (term26 l m) = (term24 l m).
Proof. exact (@lem17362 (real_lt l m) (term27 l m)). Qed.
Lemma lem5323740 (l : real) (m : real) : (term26 l m) = (term25 l m).
Proof. exact (TRANS (@lem5323739 l m) (@lem5323738 l m)). Qed.
Lemma lem5323742 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5323743 (t : real -> Prop) (l : real) (m : real) : (term29 t l m) = (term30 t l m).
Proof. exact (MK_COMB (@lem5323742 t) (@lem5323740 l m)). Qed.
Lemma lem5323744 (t : real -> Prop) (l : real) (m : real) : (term31 t l m) = (term29 t l m).
Proof. exact (@lem17362 (term12 t) (term32 l m)). Qed.
Lemma lem5323745 (t : real -> Prop) (l : real) (m : real) : (term31 t l m) = (term30 t l m).
Proof. exact (TRANS (@lem5323744 t l m) (@lem5323743 t l m)). Qed.
Lemma lem5323747 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5323748 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term33 s t l m) = (term34 s t l m).
Proof. exact (MK_COMB (@lem5323747 s) (@lem5323745 t l m)). Qed.
Lemma lem5323749 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term35 s t l m) = (term33 s t l m).
Proof. exact (@lem17362 (term12 s) (term36 t l m)). Qed.
Lemma lem5323777 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term35 s t l m) = (term34 s t l m).
Proof. exact (TRANS (@lem5323749 s t l m) (@lem5323748 s t l m)). Qed.
Lemma lem5323780 (m : real) (l : real) : (real_lt l m) = (term37 m l).
Proof. exact (@lem1988285 m l). Qed.
Lemma lem5323786 (m : real) (l : real) : (real_sub m l) = (term38 m l).
Proof. exact (@lem1982792 m l). Qed.
Lemma lem5323791 (l : real) (m : real) : (term38 m l) = (term39 l m).
Proof. exact (@lem1982761 (term40 l) m). Qed.
Lemma lem5323793 (l : real) (m : real) : (real_sub m l) = (term39 l m).
Proof. exact (TRANS (@lem5323786 m l) (@lem5323791 l m)). Qed.
Lemma lem5323794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5323795 (l : real) (m : real) : (term41 m l) = (term42 l m).
Proof. exact (MK_COMB (@lem5323794) (@lem5323793 l m)). Qed.
Lemma lem5323796 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5323797 (l : real) (m : real) : (term37 m l) = (term44 l m).
Proof. exact (MK_COMB (@lem5323795 l m) (@lem5323796)). Qed.
Lemma lem5323798 (l : real) (m : real) : (real_lt l m) = (term44 l m).
Proof. exact (TRANS (@lem5323780 m l) (@lem5323797 l m)). Qed.
Lemma lem5323799 (l : real) (m : real) : (term45 l m) = (term46 l m).
Proof. exact (@lem1988295 l (term47 l m)). Qed.
Lemma lem5323801 (x : real) (y : real) : (real_div x y) = (term48 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5323802 (l : real) (m : real) : (term47 l m) = (term49 l m).
Proof. exact (@lem5323801 (real_add l m) term50). Qed.
Lemma lem5323807 (n : nat) : (term51 n) = (term52 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5323809 : term53 = term54.
Proof. exact (@lem5323807 term55). Qed.
Lemma lem5323818 (l : real) (m : real) : (term56 l m) = (term56 l m).
Proof. exact (eq_refl (term56 l m)). Qed.
Lemma lem5323819 (l : real) (m : real) : (term49 l m) = (term57 l m).
Proof. exact (MK_COMB (@lem5323818 l m) (@lem5323809)). Qed.
Lemma lem5323820 (l : real) (m : real) : (term57 l m) = (term58 l m).
Proof. exact (@lem1982725 term54 (real_add l m)). Qed.
Lemma lem5323827 (l : real) (m : real) : (term58 l m) = (term59 l m).
Proof. exact (@lem1982781 l term54 m). Qed.
Lemma lem5323828 (l : real) (m : real) : (term57 l m) = (term59 l m).
Proof. exact (TRANS (@lem5323820 l m) (@lem5323827 l m)). Qed.
Lemma lem5323829 (l : real) (m : real) : (term49 l m) = (term59 l m).
Proof. exact (TRANS (@lem5323819 l m) (@lem5323828 l m)). Qed.
Lemma lem5323830 (l : real) (m : real) : (term47 l m) = (term59 l m).
Proof. exact (TRANS (@lem5323802 l m) (@lem5323829 l m)). Qed.
Lemma lem5323833 (l : real) : (real_sub l) = (real_sub l).
Proof. exact (eq_refl (real_sub l)). Qed.
Lemma lem5323834 (l : real) (m : real) : (term60 l m) = (term61 l m).
Proof. exact (MK_COMB (@lem5323833 l) (@lem5323830 l m)). Qed.
Lemma lem5323835 (l : real) (m : real) : (term61 l m) = (term62 l m).
Proof. exact (@lem1982792 l (term59 l m)). Qed.
Lemma lem5323836 (l : real) (m : real) : (term63 l m) = (term64 l m).
Proof. exact (@lem1982781 (term65 l) term66 (term65 m)). Qed.
Lemma lem5323837 (m : real) : (term67 m) = (term68 m).
Proof. exact (@lem1982749 term66 term54 m). Qed.
Lemma lem5323838 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem5323840 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5323841 : term66 = term71.
Proof. exact (@lem5323840 term72). Qed.
Lemma lem5323842 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323843 : term73 = term74.
Proof. exact (MK_COMB (@lem5323842) (@lem5323841)). Qed.
Lemma lem5323844 : term75 = term76.
Proof. exact (MK_COMB (@lem5323843) (@lem5323838)). Qed.
Lemma lem5323845 : term76 = term77.
Proof. exact (@lem1981613 term66 term78 term78 term50). Qed.
Lemma lem5323847 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323848 : term81 = term82.
Proof. exact (@lem5323847 term72 term55). Qed.
Lemma lem5323849 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5323850 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5323851 : term85 = term55.
Proof. exact (EQ_MP (@lem5323850) (@lem5323849)). Qed.
Lemma lem5323852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323853 : term82 = term50.
Proof. exact (MK_COMB (@lem5323852) (@lem5323851)). Qed.
Lemma lem5323854 : term81 = term50.
Proof. exact (TRANS (@lem5323848) (@lem5323853)). Qed.
Lemma lem5323856 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5323857 : term88 = term89.
Proof. exact (@lem5323856 term72 term72). Qed.
Lemma lem5323858 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323859 : term91 = term72.
Proof. exact (EQ_MP (@lem5323858) (@lem940073)). Qed.
Lemma lem5323860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323861 : term92 = term78.
Proof. exact (MK_COMB (@lem5323860) (@lem5323859)). Qed.
Lemma lem5323862 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5323863 : term89 = term66.
Proof. exact (MK_COMB (@lem5323862) (@lem5323861)). Qed.
Lemma lem5323864 : term88 = term66.
Proof. exact (TRANS (@lem5323857) (@lem5323863)). Qed.
Lemma lem5323865 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5323866 : term93 = term94.
Proof. exact (MK_COMB (@lem5323865) (@lem5323864)). Qed.
Lemma lem5323867 : term77 = term95.
Proof. exact (MK_COMB (@lem5323866) (@lem5323854)). Qed.
Lemma lem5323868 : term76 = term95.
Proof. exact (TRANS (@lem5323845) (@lem5323867)). Qed.
Lemma lem5323871 : term75 = term95.
Proof. exact (TRANS (@lem5323844) (@lem5323868)). Qed.
Lemma lem5323872 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323873 : term96 = term97.
Proof. exact (MK_COMB (@lem5323872) (@lem5323871)). Qed.
Lemma lem5323874 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5323875 (m : real) : (term68 m) = (term98 m).
Proof. exact (MK_COMB (@lem5323873) (@lem5323874 m)). Qed.
Lemma lem5323876 (m : real) : (term67 m) = (term98 m).
Proof. exact (TRANS (@lem5323837 m) (@lem5323875 m)). Qed.
Lemma lem5323877 (l : real) : (term67 l) = (term68 l).
Proof. exact (@lem1982749 term66 term54 l). Qed.
Lemma lem5323878 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem5323880 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5323881 : term66 = term71.
Proof. exact (@lem5323880 term72). Qed.
Lemma lem5323882 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323883 : term73 = term74.
Proof. exact (MK_COMB (@lem5323882) (@lem5323881)). Qed.
Lemma lem5323884 : term75 = term76.
Proof. exact (MK_COMB (@lem5323883) (@lem5323878)). Qed.
Lemma lem5323885 : term76 = term77.
Proof. exact (@lem1981613 term66 term78 term78 term50). Qed.
Lemma lem5323887 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323888 : term81 = term82.
Proof. exact (@lem5323887 term72 term55). Qed.
Lemma lem5323889 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5323890 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5323891 : term85 = term55.
Proof. exact (EQ_MP (@lem5323890) (@lem5323889)). Qed.
Lemma lem5323892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323893 : term82 = term50.
Proof. exact (MK_COMB (@lem5323892) (@lem5323891)). Qed.
Lemma lem5323894 : term81 = term50.
Proof. exact (TRANS (@lem5323888) (@lem5323893)). Qed.
Lemma lem5323896 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5323897 : term88 = term89.
Proof. exact (@lem5323896 term72 term72). Qed.
Lemma lem5323898 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323899 : term91 = term72.
Proof. exact (EQ_MP (@lem5323898) (@lem940073)). Qed.
Lemma lem5323900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323901 : term92 = term78.
Proof. exact (MK_COMB (@lem5323900) (@lem5323899)). Qed.
Lemma lem5323902 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5323903 : term89 = term66.
Proof. exact (MK_COMB (@lem5323902) (@lem5323901)). Qed.
Lemma lem5323904 : term88 = term66.
Proof. exact (TRANS (@lem5323897) (@lem5323903)). Qed.
Lemma lem5323905 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5323906 : term93 = term94.
Proof. exact (MK_COMB (@lem5323905) (@lem5323904)). Qed.
Lemma lem5323907 : term77 = term95.
Proof. exact (MK_COMB (@lem5323906) (@lem5323894)). Qed.
Lemma lem5323908 : term76 = term95.
Proof. exact (TRANS (@lem5323885) (@lem5323907)). Qed.
Lemma lem5323911 : term75 = term95.
Proof. exact (TRANS (@lem5323884) (@lem5323908)). Qed.
Lemma lem5323912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323913 : term96 = term97.
Proof. exact (MK_COMB (@lem5323912) (@lem5323911)). Qed.
Lemma lem5323914 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5323915 (l : real) : (term68 l) = (term98 l).
Proof. exact (MK_COMB (@lem5323913) (@lem5323914 l)). Qed.
Lemma lem5323916 (l : real) : (term67 l) = (term98 l).
Proof. exact (TRANS (@lem5323877 l) (@lem5323915 l)). Qed.
Lemma lem5323917 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323918 (l : real) : (term99 l) = (term100 l).
Proof. exact (MK_COMB (@lem5323917) (@lem5323916 l)). Qed.
Lemma lem5323919 (l : real) (m : real) : (term64 l m) = (term101 l m).
Proof. exact (MK_COMB (@lem5323918 l) (@lem5323876 m)). Qed.
Lemma lem5323920 (l : real) (m : real) : (term63 l m) = (term101 l m).
Proof. exact (TRANS (@lem5323836 l m) (@lem5323919 l m)). Qed.
Lemma lem5323921 (l : real) : (real_add l) = (real_add l).
Proof. exact (eq_refl (real_add l)). Qed.
Lemma lem5323922 (l : real) (m : real) : (term62 l m) = (term102 l m).
Proof. exact (MK_COMB (@lem5323921 l) (@lem5323920 l m)). Qed.
Lemma lem5323923 (l : real) (m : real) : (term102 l m) = (term103 l m).
Proof. exact (@lem1982763 l (term98 l) (term98 m)). Qed.
Lemma lem5323924 (l : real) : (term104 l) = (term105 l).
Proof. exact (@lem1982715 term95 l). Qed.
Lemma lem5323926 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323927 : term78 = term107.
Proof. exact (@lem5323926 term72). Qed.
Lemma lem5323930 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem5323931 : term109 = term110.
Proof. exact (MK_COMB (@lem5323930) (@lem5323927)). Qed.
Lemma lem5323932 : term111.
Proof. exact (@lem1981473 term66 term50 term78 term78 term78 term50). Qed.
Lemma lem5323934 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323935 : term113 = term114.
Proof. exact (@lem5323934 (NUMERAL 0) term55). Qed.
Lemma lem5323936 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5323937 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5323938 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5323937 h1) (fun h1 : term114 = True => @lem5323936)). Qed.
Lemma lem5323939 : term114 = True.
Proof. exact (EQ_MP (@lem5323938) (@lem5323936)). Qed.
Lemma lem5323940 : term113 = True.
Proof. exact (TRANS (@lem5323935) (@lem5323939)). Qed.
Lemma lem5323941 : True = term113.
Proof. exact (SYM (@lem5323940)). Qed.
Lemma lem5323942 : term113.
Proof. exact (EQ_MP (@lem5323941) (@lem0)). Qed.
Lemma lem5323943 : term116.
Proof. exact (@lem5323932 (@lem5323942)). Qed.
Lemma lem5323945 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323946 : term117 = term118.
Proof. exact (@lem5323945 (NUMERAL 0) term72). Qed.
Lemma lem5323947 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323948 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323949 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5323948 h1) (fun h1 : term118 = True => @lem5323947)). Qed.
Lemma lem5323950 : term118 = True.
Proof. exact (EQ_MP (@lem5323949) (@lem5323947)). Qed.
Lemma lem5323951 : term117 = True.
Proof. exact (TRANS (@lem5323946) (@lem5323950)). Qed.
Lemma lem5323952 : True = term117.
Proof. exact (SYM (@lem5323951)). Qed.
Lemma lem5323953 : term117.
Proof. exact (EQ_MP (@lem5323952) (@lem0)). Qed.
Lemma lem5323954 : term120.
Proof. exact (@lem5323943 (@lem5323953)). Qed.
Lemma lem5323956 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323957 : term113 = term114.
Proof. exact (@lem5323956 (NUMERAL 0) term55). Qed.
Lemma lem5323958 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5323959 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5323960 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5323959 h1) (fun h1 : term114 = True => @lem5323958)). Qed.
Lemma lem5323961 : term114 = True.
Proof. exact (EQ_MP (@lem5323960) (@lem5323958)). Qed.
Lemma lem5323962 : term113 = True.
Proof. exact (TRANS (@lem5323957) (@lem5323961)). Qed.
Lemma lem5323963 : True = term113.
Proof. exact (SYM (@lem5323962)). Qed.
Lemma lem5323964 : term113.
Proof. exact (EQ_MP (@lem5323963) (@lem0)). Qed.
Lemma lem5323965 : term121.
Proof. exact (@lem5323954 (@lem5323964)). Qed.
Lemma lem5323967 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323968 : term81 = term82.
Proof. exact (@lem5323967 term72 term55). Qed.
Lemma lem5323969 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5323970 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5323971 : term85 = term55.
Proof. exact (EQ_MP (@lem5323970) (@lem5323969)). Qed.
Lemma lem5323972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323973 : term82 = term50.
Proof. exact (MK_COMB (@lem5323972) (@lem5323971)). Qed.
Lemma lem5323974 : term81 = term50.
Proof. exact (TRANS (@lem5323968) (@lem5323973)). Qed.
Lemma lem5323976 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5323977 : term88 = term89.
Proof. exact (@lem5323976 term72 term72). Qed.
Lemma lem5323978 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323979 : term91 = term72.
Proof. exact (EQ_MP (@lem5323978) (@lem940073)). Qed.
Lemma lem5323980 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323981 : term92 = term78.
Proof. exact (MK_COMB (@lem5323980) (@lem5323979)). Qed.
Lemma lem5323982 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5323983 : term89 = term66.
Proof. exact (MK_COMB (@lem5323982) (@lem5323981)). Qed.
Lemma lem5323984 : term88 = term66.
Proof. exact (TRANS (@lem5323977) (@lem5323983)). Qed.
Lemma lem5323985 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323986 : term122 = term123.
Proof. exact (MK_COMB (@lem5323985) (@lem5323984)). Qed.
Lemma lem5323987 : term124 = term125.
Proof. exact (MK_COMB (@lem5323986) (@lem5323974)). Qed.
Lemma lem5323990 : term126 = term78.
Proof. exact (@lem1367765 term72 term72). Qed.
Lemma lem5323991 : term127 = term84.
Proof. exact (@lem706885). Qed.
Lemma lem5323992 : (term127 = term84) = (term128 = term55).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term84). Qed.
Lemma lem5323993 : term128 = term55.
Proof. exact (EQ_MP (@lem5323992) (@lem5323991)). Qed.
Lemma lem5323994 : term55 = term128.
Proof. exact (SYM (@lem5323993)). Qed.
Lemma lem5323995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323996 : term50 = term129.
Proof. exact (MK_COMB (@lem5323995) (@lem5323994)). Qed.
Lemma lem5323997 : term123 = term123.
Proof. exact (eq_refl term123). Qed.
Lemma lem5323998 : term125 = term126.
Proof. exact (MK_COMB (@lem5323997) (@lem5323996)). Qed.
Lemma lem5323999 : term125 = term78.
Proof. exact (TRANS (@lem5323998) (@lem5323990)). Qed.
Lemma lem5324000 : term124 = term78.
Proof. exact (TRANS (@lem5323987) (@lem5323999)). Qed.
Lemma lem5324001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324002 : term130 = term131.
Proof. exact (MK_COMB (@lem5324001) (@lem5324000)). Qed.
Lemma lem5324003 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem5324004 : term132 = term81.
Proof. exact (MK_COMB (@lem5324002) (@lem5324003)). Qed.
Lemma lem5324006 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324007 : term81 = term82.
Proof. exact (@lem5324006 term72 term55). Qed.
Lemma lem5324008 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324009 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324010 : term85 = term55.
Proof. exact (EQ_MP (@lem5324009) (@lem5324008)). Qed.
Lemma lem5324011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324012 : term82 = term50.
Proof. exact (MK_COMB (@lem5324011) (@lem5324010)). Qed.
Lemma lem5324013 : term81 = term50.
Proof. exact (TRANS (@lem5324007) (@lem5324012)). Qed.
Lemma lem5324014 : term132 = term50.
Proof. exact (TRANS (@lem5324004) (@lem5324013)). Qed.
Lemma lem5324016 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324017 : term133 = term134.
Proof. exact (@lem5324016 term55 term72). Qed.
Lemma lem5324018 : term135 = term84.
Proof. exact (@lem996237 term84). Qed.
Lemma lem5324019 : (term135 = term84) = (term136 = term55).
Proof. exact (@lem1007663 term84 (BIT1 0) term84). Qed.
Lemma lem5324020 : term136 = term55.
Proof. exact (EQ_MP (@lem5324019) (@lem5324018)). Qed.
Lemma lem5324021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324022 : term134 = term50.
Proof. exact (MK_COMB (@lem5324021) (@lem5324020)). Qed.
Lemma lem5324023 : term133 = term50.
Proof. exact (TRANS (@lem5324017) (@lem5324022)). Qed.
Lemma lem5324024 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem5324025 : term137 = term81.
Proof. exact (MK_COMB (@lem5324024) (@lem5324023)). Qed.
Lemma lem5324027 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324028 : term81 = term82.
Proof. exact (@lem5324027 term72 term55). Qed.
Lemma lem5324029 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324030 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324031 : term85 = term55.
Proof. exact (EQ_MP (@lem5324030) (@lem5324029)). Qed.
Lemma lem5324032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324033 : term82 = term50.
Proof. exact (MK_COMB (@lem5324032) (@lem5324031)). Qed.
Lemma lem5324034 : term81 = term50.
Proof. exact (TRANS (@lem5324028) (@lem5324033)). Qed.
Lemma lem5324035 : term137 = term50.
Proof. exact (TRANS (@lem5324025) (@lem5324034)). Qed.
Lemma lem5324036 : term50 = term137.
Proof. exact (SYM (@lem5324035)). Qed.
Lemma lem5324037 : term132 = term137.
Proof. exact (TRANS (@lem5324014) (@lem5324036)). Qed.
Lemma lem5324038 : term110 = term54.
Proof. exact (@lem5323965 (@lem5324037)). Qed.
Lemma lem5324041 : term109 = term54.
Proof. exact (TRANS (@lem5323931) (@lem5324038)). Qed.
Lemma lem5324042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324043 : term138 = term139.
Proof. exact (MK_COMB (@lem5324042) (@lem5324041)). Qed.
Lemma lem5324044 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5324045 (l : real) : (term105 l) = (term65 l).
Proof. exact (MK_COMB (@lem5324043) (@lem5324044 l)). Qed.
Lemma lem5324046 (l : real) : (term104 l) = (term65 l).
Proof. exact (TRANS (@lem5323924 l) (@lem5324045 l)). Qed.
Lemma lem5324047 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324048 (l : real) : (term140 l) = (term141 l).
Proof. exact (MK_COMB (@lem5324047) (@lem5324046 l)). Qed.
Lemma lem5324049 (m : real) : (term98 m) = (term98 m).
Proof. exact (eq_refl (term98 m)). Qed.
Lemma lem5324050 (l : real) (m : real) : (term103 l m) = (term142 l m).
Proof. exact (MK_COMB (@lem5324048 l) (@lem5324049 m)). Qed.
Lemma lem5324051 (l : real) (m : real) : (term102 l m) = (term142 l m).
Proof. exact (TRANS (@lem5323923 l m) (@lem5324050 l m)). Qed.
Lemma lem5324052 (l : real) (m : real) : (term62 l m) = (term142 l m).
Proof. exact (TRANS (@lem5323922 l m) (@lem5324051 l m)). Qed.
Lemma lem5324053 (l : real) (m : real) : (term61 l m) = (term142 l m).
Proof. exact (TRANS (@lem5323835 l m) (@lem5324052 l m)). Qed.
Lemma lem5324054 (l : real) (m : real) : (term60 l m) = (term142 l m).
Proof. exact (TRANS (@lem5323834 l m) (@lem5324053 l m)). Qed.
Lemma lem5324055 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5324056 (l : real) (m : real) : (term143 l m) = (term144 l m).
Proof. exact (MK_COMB (@lem5324055) (@lem5324054 l m)). Qed.
Lemma lem5324057 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324058 (l : real) (m : real) : (term46 l m) = (term145 l m).
Proof. exact (MK_COMB (@lem5324056 l m) (@lem5324057)). Qed.
Lemma lem5324059 (l : real) (m : real) : (term45 l m) = (term145 l m).
Proof. exact (TRANS (@lem5323799 l m) (@lem5324058 l m)). Qed.
Lemma lem5324060 (l : real) (m : real) : (term146 l m) = (term147 l m).
Proof. exact (@lem1988295 (term47 l m) m). Qed.
Lemma lem5324061 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5324063 (x : real) (y : real) : (real_div x y) = (term48 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5324064 (l : real) (m : real) : (term47 l m) = (term49 l m).
Proof. exact (@lem5324063 (real_add l m) term50). Qed.
Lemma lem5324069 (n : nat) : (term51 n) = (term52 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5324071 : term53 = term54.
Proof. exact (@lem5324069 term55). Qed.
Lemma lem5324080 (l : real) (m : real) : (term56 l m) = (term56 l m).
Proof. exact (eq_refl (term56 l m)). Qed.
Lemma lem5324081 (l : real) (m : real) : (term49 l m) = (term57 l m).
Proof. exact (MK_COMB (@lem5324080 l m) (@lem5324071)). Qed.
Lemma lem5324082 (l : real) (m : real) : (term57 l m) = (term58 l m).
Proof. exact (@lem1982725 term54 (real_add l m)). Qed.
Lemma lem5324089 (l : real) (m : real) : (term58 l m) = (term59 l m).
Proof. exact (@lem1982781 l term54 m). Qed.
Lemma lem5324090 (l : real) (m : real) : (term57 l m) = (term59 l m).
Proof. exact (TRANS (@lem5324082 l m) (@lem5324089 l m)). Qed.
Lemma lem5324091 (l : real) (m : real) : (term49 l m) = (term59 l m).
Proof. exact (TRANS (@lem5324081 l m) (@lem5324090 l m)). Qed.
Lemma lem5324092 (l : real) (m : real) : (term47 l m) = (term59 l m).
Proof. exact (TRANS (@lem5324064 l m) (@lem5324091 l m)). Qed.
Lemma lem5324093 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5324094 (l : real) (m : real) : (term148 l m) = (term149 l m).
Proof. exact (MK_COMB (@lem5324093) (@lem5324092 l m)). Qed.
Lemma lem5324095 (l : real) (m : real) : (term150 l m) = (term151 l m).
Proof. exact (MK_COMB (@lem5324094 l m) (@lem5324061 m)). Qed.
Lemma lem5324096 (l : real) (m : real) : (term151 l m) = (term152 l m).
Proof. exact (@lem1982792 (term59 l m) m). Qed.
Lemma lem5324100 (l : real) (m : real) : (term152 l m) = (term153 l m).
Proof. exact (@lem1982755 (term65 l) (term65 m) (term40 m)). Qed.
Lemma lem5324101 (m : real) : (term154 m) = (term155 m).
Proof. exact (@lem1982711 term54 term66 m). Qed.
Lemma lem5324103 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5324104 : term66 = term71.
Proof. exact (@lem5324103 term72). Qed.
Lemma lem5324107 : term156 = term156.
Proof. exact (eq_refl term156). Qed.
Lemma lem5324108 : term157 = term158.
Proof. exact (MK_COMB (@lem5324107) (@lem5324104)). Qed.
Lemma lem5324109 : term159.
Proof. exact (@lem1981473 term78 term50 term66 term78 term66 term50). Qed.
Lemma lem5324111 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324112 : term113 = term114.
Proof. exact (@lem5324111 (NUMERAL 0) term55). Qed.
Lemma lem5324113 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324114 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324115 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324114 h1) (fun h1 : term114 = True => @lem5324113)). Qed.
Lemma lem5324116 : term114 = True.
Proof. exact (EQ_MP (@lem5324115) (@lem5324113)). Qed.
Lemma lem5324117 : term113 = True.
Proof. exact (TRANS (@lem5324112) (@lem5324116)). Qed.
Lemma lem5324118 : True = term113.
Proof. exact (SYM (@lem5324117)). Qed.
Lemma lem5324119 : term113.
Proof. exact (EQ_MP (@lem5324118) (@lem0)). Qed.
Lemma lem5324120 : term160.
Proof. exact (@lem5324109 (@lem5324119)). Qed.
Lemma lem5324122 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324123 : term117 = term118.
Proof. exact (@lem5324122 (NUMERAL 0) term72). Qed.
Lemma lem5324124 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324125 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324126 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324125 h1) (fun h1 : term118 = True => @lem5324124)). Qed.
Lemma lem5324127 : term118 = True.
Proof. exact (EQ_MP (@lem5324126) (@lem5324124)). Qed.
Lemma lem5324128 : term117 = True.
Proof. exact (TRANS (@lem5324123) (@lem5324127)). Qed.
Lemma lem5324129 : True = term117.
Proof. exact (SYM (@lem5324128)). Qed.
Lemma lem5324130 : term117.
Proof. exact (EQ_MP (@lem5324129) (@lem0)). Qed.
Lemma lem5324131 : term161.
Proof. exact (@lem5324120 (@lem5324130)). Qed.
Lemma lem5324133 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324134 : term113 = term114.
Proof. exact (@lem5324133 (NUMERAL 0) term55). Qed.
Lemma lem5324135 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324136 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324137 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324136 h1) (fun h1 : term114 = True => @lem5324135)). Qed.
Lemma lem5324138 : term114 = True.
Proof. exact (EQ_MP (@lem5324137) (@lem5324135)). Qed.
Lemma lem5324139 : term113 = True.
Proof. exact (TRANS (@lem5324134) (@lem5324138)). Qed.
Lemma lem5324140 : True = term113.
Proof. exact (SYM (@lem5324139)). Qed.
Lemma lem5324141 : term113.
Proof. exact (EQ_MP (@lem5324140) (@lem0)). Qed.
Lemma lem5324142 : term162.
Proof. exact (@lem5324131 (@lem5324141)). Qed.
Lemma lem5324144 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5324145 : term163 = term164.
Proof. exact (@lem5324144 term72 term55). Qed.
Lemma lem5324146 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324147 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324148 : term85 = term55.
Proof. exact (EQ_MP (@lem5324147) (@lem5324146)). Qed.
Lemma lem5324149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324150 : term82 = term50.
Proof. exact (MK_COMB (@lem5324149) (@lem5324148)). Qed.
Lemma lem5324151 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324152 : term164 = term165.
Proof. exact (MK_COMB (@lem5324151) (@lem5324150)). Qed.
Lemma lem5324153 : term163 = term165.
Proof. exact (TRANS (@lem5324145) (@lem5324152)). Qed.
Lemma lem5324155 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324156 : term166 = term92.
Proof. exact (@lem5324155 term72 term72). Qed.
Lemma lem5324157 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324158 : term91 = term72.
Proof. exact (EQ_MP (@lem5324157) (@lem940073)). Qed.
Lemma lem5324159 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324160 : term92 = term78.
Proof. exact (MK_COMB (@lem5324159) (@lem5324158)). Qed.
Lemma lem5324161 : term166 = term78.
Proof. exact (TRANS (@lem5324156) (@lem5324160)). Qed.
Lemma lem5324162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324163 : term167 = term168.
Proof. exact (MK_COMB (@lem5324162) (@lem5324161)). Qed.
Lemma lem5324164 : term169 = term170.
Proof. exact (MK_COMB (@lem5324163) (@lem5324153)). Qed.
Lemma lem5324167 : term171 = term66.
Proof. exact (@lem1367771 term72 term72). Qed.
Lemma lem5324168 : term127 = term84.
Proof. exact (@lem706885). Qed.
Lemma lem5324169 : (term127 = term84) = (term128 = term55).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term84). Qed.
Lemma lem5324170 : term128 = term55.
Proof. exact (EQ_MP (@lem5324169) (@lem5324168)). Qed.
Lemma lem5324171 : term55 = term128.
Proof. exact (SYM (@lem5324170)). Qed.
Lemma lem5324172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324173 : term50 = term129.
Proof. exact (MK_COMB (@lem5324172) (@lem5324171)). Qed.
Lemma lem5324174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324175 : term165 = term172.
Proof. exact (MK_COMB (@lem5324174) (@lem5324173)). Qed.
Lemma lem5324176 : term168 = term168.
Proof. exact (eq_refl term168). Qed.
Lemma lem5324177 : term170 = term171.
Proof. exact (MK_COMB (@lem5324176) (@lem5324175)). Qed.
Lemma lem5324178 : term170 = term66.
Proof. exact (TRANS (@lem5324177) (@lem5324167)). Qed.
Lemma lem5324179 : term169 = term66.
Proof. exact (TRANS (@lem5324164) (@lem5324178)). Qed.
Lemma lem5324180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324181 : term173 = term73.
Proof. exact (MK_COMB (@lem5324180) (@lem5324179)). Qed.
Lemma lem5324182 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem5324183 : term174 = term163.
Proof. exact (MK_COMB (@lem5324181) (@lem5324182)). Qed.
Lemma lem5324185 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5324186 : term163 = term164.
Proof. exact (@lem5324185 term72 term55). Qed.
Lemma lem5324187 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324188 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324189 : term85 = term55.
Proof. exact (EQ_MP (@lem5324188) (@lem5324187)). Qed.
Lemma lem5324190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324191 : term82 = term50.
Proof. exact (MK_COMB (@lem5324190) (@lem5324189)). Qed.
Lemma lem5324192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324193 : term164 = term165.
Proof. exact (MK_COMB (@lem5324192) (@lem5324191)). Qed.
Lemma lem5324194 : term163 = term165.
Proof. exact (TRANS (@lem5324186) (@lem5324193)). Qed.
Lemma lem5324195 : term174 = term165.
Proof. exact (TRANS (@lem5324183) (@lem5324194)). Qed.
Lemma lem5324197 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324198 : term133 = term134.
Proof. exact (@lem5324197 term55 term72). Qed.
Lemma lem5324199 : term135 = term84.
Proof. exact (@lem996237 term84). Qed.
Lemma lem5324200 : (term135 = term84) = (term136 = term55).
Proof. exact (@lem1007663 term84 (BIT1 0) term84). Qed.
Lemma lem5324201 : term136 = term55.
Proof. exact (EQ_MP (@lem5324200) (@lem5324199)). Qed.
Lemma lem5324202 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324203 : term134 = term50.
Proof. exact (MK_COMB (@lem5324202) (@lem5324201)). Qed.
Lemma lem5324204 : term133 = term50.
Proof. exact (TRANS (@lem5324198) (@lem5324203)). Qed.
Lemma lem5324205 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem5324206 : term175 = term163.
Proof. exact (MK_COMB (@lem5324205) (@lem5324204)). Qed.
Lemma lem5324208 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5324209 : term163 = term164.
Proof. exact (@lem5324208 term72 term55). Qed.
Lemma lem5324210 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324211 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324212 : term85 = term55.
Proof. exact (EQ_MP (@lem5324211) (@lem5324210)). Qed.
Lemma lem5324213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324214 : term82 = term50.
Proof. exact (MK_COMB (@lem5324213) (@lem5324212)). Qed.
Lemma lem5324215 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324216 : term164 = term165.
Proof. exact (MK_COMB (@lem5324215) (@lem5324214)). Qed.
Lemma lem5324217 : term163 = term165.
Proof. exact (TRANS (@lem5324209) (@lem5324216)). Qed.
Lemma lem5324218 : term175 = term165.
Proof. exact (TRANS (@lem5324206) (@lem5324217)). Qed.
Lemma lem5324219 : term165 = term175.
Proof. exact (SYM (@lem5324218)). Qed.
Lemma lem5324220 : term174 = term175.
Proof. exact (TRANS (@lem5324195) (@lem5324219)). Qed.
Lemma lem5324221 : term158 = term95.
Proof. exact (@lem5324142 (@lem5324220)). Qed.
Lemma lem5324224 : term157 = term95.
Proof. exact (TRANS (@lem5324108) (@lem5324221)). Qed.
Lemma lem5324225 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324226 : term176 = term97.
Proof. exact (MK_COMB (@lem5324225) (@lem5324224)). Qed.
Lemma lem5324227 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5324228 (m : real) : (term155 m) = (term98 m).
Proof. exact (MK_COMB (@lem5324226) (@lem5324227 m)). Qed.
Lemma lem5324229 (m : real) : (term154 m) = (term98 m).
Proof. exact (TRANS (@lem5324101 m) (@lem5324228 m)). Qed.
Lemma lem5324230 (l : real) : (term141 l) = (term141 l).
Proof. exact (eq_refl (term141 l)). Qed.
Lemma lem5324231 (l : real) (m : real) : (term153 l m) = (term142 l m).
Proof. exact (MK_COMB (@lem5324230 l) (@lem5324229 m)). Qed.
Lemma lem5324233 (l : real) (m : real) : (term152 l m) = (term142 l m).
Proof. exact (TRANS (@lem5324100 l m) (@lem5324231 l m)). Qed.
Lemma lem5324234 (l : real) (m : real) : (term151 l m) = (term142 l m).
Proof. exact (TRANS (@lem5324096 l m) (@lem5324233 l m)). Qed.
Lemma lem5324235 (l : real) (m : real) : (term150 l m) = (term142 l m).
Proof. exact (TRANS (@lem5324095 l m) (@lem5324234 l m)). Qed.
Lemma lem5324236 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5324237 (l : real) (m : real) : (term177 l m) = (term144 l m).
Proof. exact (MK_COMB (@lem5324236) (@lem5324235 l m)). Qed.
Lemma lem5324238 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324239 (l : real) (m : real) : (term147 l m) = (term145 l m).
Proof. exact (MK_COMB (@lem5324237 l m) (@lem5324238)). Qed.
Lemma lem5324240 (l : real) (m : real) : (term146 l m) = (term145 l m).
Proof. exact (TRANS (@lem5324060 l m) (@lem5324239 l m)). Qed.
Lemma lem5324241 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5324242 (l : real) (m : real) : (term178 l m) = (term179 l m).
Proof. exact (MK_COMB (@lem5324241) (@lem5324059 l m)). Qed.
Lemma lem5324243 (l : real) (m : real) : (term20 l m) = (term180 l m).
Proof. exact (MK_COMB (@lem5324242 l m) (@lem5324240 l m)). Qed.
Lemma lem5324244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5324245 (l : real) (m : real) : (term23 l m) = (term181 l m).
Proof. exact (MK_COMB (@lem5324244) (@lem5323798 l m)). Qed.
Lemma lem5324246 (l : real) (m : real) : (term25 l m) = (term182 l m).
Proof. exact (MK_COMB (@lem5324245 l m) (@lem5324243 l m)). Qed.
Lemma lem5324248 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5324249 (t : real -> Prop) (l : real) (m : real) : (term30 t l m) = (term183 t l m).
Proof. exact (MK_COMB (@lem5324248 t) (@lem5324246 l m)). Qed.
Lemma lem5324251 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5324252 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term34 s t l m) = (term184 s t l m).
Proof. exact (MK_COMB (@lem5324251 s) (@lem5324249 t l m)). Qed.
Lemma lem5324259 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term35 s t l m) = (term184 s t l m).
Proof. exact (TRANS (@lem5323777 s t l m) (@lem5324252 s t l m)). Qed.
Lemma lem5324276 (l : real) (m : real) : (term182 l m) = (term185 l m).
Proof. exact (@lem19158 (term145 l m) (term44 l m) (term145 l m)). Qed.
Lemma lem5324279 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5324280 (t : real -> Prop) (l : real) (m : real) : (term183 t l m) = (term186 t l m).
Proof. exact (MK_COMB (@lem5324279 t) (@lem5324276 l m)). Qed.
Lemma lem5324287 (t : real -> Prop) (l : real) (m : real) : (term186 t l m) = (term187 t l m).
Proof. exact (@lem19158 (term188 l m) (term12 t) (term188 l m)). Qed.
Lemma lem5324288 (t : real -> Prop) (l : real) (m : real) : (term183 t l m) = (term187 t l m).
Proof. exact (TRANS (@lem5324280 t l m) (@lem5324287 t l m)). Qed.
Lemma lem5324291 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5324292 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term184 s t l m) = (term189 s t l m).
Proof. exact (MK_COMB (@lem5324291 s) (@lem5324288 t l m)). Qed.
Lemma lem5324299 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term189 s t l m) = (term190 s t l m).
Proof. exact (@lem19158 (term191 t l m) (term12 s) (term191 t l m)). Qed.
Lemma lem5324300 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term184 s t l m) = (term190 s t l m).
Proof. exact (TRANS (@lem5324292 s t l m) (@lem5324299 s t l m)). Qed.
Lemma lem5324301 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term35 s t l m) = (term190 s t l m).
Proof. exact (TRANS (@lem5324259 s t l m) (@lem5324300 s t l m)). Qed.
Lemma lem5324311 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term190 s t l m.
Proof. exact (h1). Qed.
Lemma lem5324312 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term192 s t l m.
Proof. exact (h1). Qed.
Lemma lem5324313 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term191 t l m.
Proof. exact (proj2 (@lem5324312 s t l m h1)). Qed.
Lemma lem5324315 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term188 l m.
Proof. exact (proj2 (@lem5324313 s t l m h1)). Qed.
Lemma lem5324317 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term145 l m.
Proof. exact (proj2 (@lem5324315 s t l m h1)). Qed.
Lemma lem5324318 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term44 l m.
Proof. exact (proj1 (@lem5324315 s t l m h1)). Qed.
Lemma lem5324320 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5324321 : term193 = term117.
Proof. exact (@lem5324320 term43 term78). Qed.
Lemma lem5324323 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324324 : term78 = term107.
Proof. exact (@lem5324323 term72). Qed.
Lemma lem5324326 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324327 : term43 = term194.
Proof. exact (@lem5324326 (NUMERAL 0)). Qed.
Lemma lem5324328 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324329 : term195 = term196.
Proof. exact (MK_COMB (@lem5324328) (@lem5324327)). Qed.
Lemma lem5324330 : term117 = term197.
Proof. exact (MK_COMB (@lem5324329) (@lem5324324)). Qed.
Lemma lem5324331 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5324333 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324334 : term117 = term118.
Proof. exact (@lem5324333 (NUMERAL 0) term72). Qed.
Lemma lem5324335 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324336 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324337 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324336 h1) (fun h1 : term118 = True => @lem5324335)). Qed.
Lemma lem5324338 : term118 = True.
Proof. exact (EQ_MP (@lem5324337) (@lem5324335)). Qed.
Lemma lem5324339 : term117 = True.
Proof. exact (TRANS (@lem5324334) (@lem5324338)). Qed.
Lemma lem5324340 : True = term117.
Proof. exact (SYM (@lem5324339)). Qed.
Lemma lem5324341 : term117.
Proof. exact (EQ_MP (@lem5324340) (@lem0)). Qed.
Lemma lem5324342 : term199.
Proof. exact (@lem5324331 (@lem5324341)). Qed.
Lemma lem5324344 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324345 : term117 = term118.
Proof. exact (@lem5324344 (NUMERAL 0) term72). Qed.
Lemma lem5324346 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324347 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324348 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324347 h1) (fun h1 : term118 = True => @lem5324346)). Qed.
Lemma lem5324349 : term118 = True.
Proof. exact (EQ_MP (@lem5324348) (@lem5324346)). Qed.
Lemma lem5324350 : term117 = True.
Proof. exact (TRANS (@lem5324345) (@lem5324349)). Qed.
Lemma lem5324351 : True = term117.
Proof. exact (SYM (@lem5324350)). Qed.
Lemma lem5324352 : term117.
Proof. exact (EQ_MP (@lem5324351) (@lem0)). Qed.
Lemma lem5324353 : term197 = term200.
Proof. exact (@lem5324342 (@lem5324352)). Qed.
Lemma lem5324355 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324356 : term166 = term92.
Proof. exact (@lem5324355 term72 term72). Qed.
Lemma lem5324357 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324358 : term91 = term72.
Proof. exact (EQ_MP (@lem5324357) (@lem940073)). Qed.
Lemma lem5324359 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324360 : term92 = term78.
Proof. exact (MK_COMB (@lem5324359) (@lem5324358)). Qed.
Lemma lem5324361 : term166 = term78.
Proof. exact (TRANS (@lem5324356) (@lem5324360)). Qed.
Lemma lem5324363 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324364 : term202 = term43.
Proof. exact (@lem5324363 term72). Qed.
Lemma lem5324365 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324366 : term203 = term195.
Proof. exact (MK_COMB (@lem5324365) (@lem5324364)). Qed.
Lemma lem5324367 : term200 = term117.
Proof. exact (MK_COMB (@lem5324366) (@lem5324361)). Qed.
Lemma lem5324369 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324370 : term117 = term118.
Proof. exact (@lem5324369 (NUMERAL 0) term72). Qed.
Lemma lem5324371 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324372 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324373 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324372 h1) (fun h1 : term118 = True => @lem5324371)). Qed.
Lemma lem5324374 : term118 = True.
Proof. exact (EQ_MP (@lem5324373) (@lem5324371)). Qed.
Lemma lem5324375 : term117 = True.
Proof. exact (TRANS (@lem5324370) (@lem5324374)). Qed.
Lemma lem5324376 : term200 = True.
Proof. exact (TRANS (@lem5324367) (@lem5324375)). Qed.
Lemma lem5324377 : term197 = True.
Proof. exact (TRANS (@lem5324353) (@lem5324376)). Qed.
Lemma lem5324378 : term117 = True.
Proof. exact (TRANS (@lem5324330) (@lem5324377)). Qed.
Lemma lem5324379 : term193 = True.
Proof. exact (TRANS (@lem5324321) (@lem5324378)). Qed.
Lemma lem5324380 : True = term193.
Proof. exact (SYM (@lem5324379)). Qed.
Lemma lem5324381 : term193.
Proof. exact (EQ_MP (@lem5324380) (@lem0)). Qed.
Lemma lem5324382 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term204 l m.
Proof. exact (conj (@lem5324381) (@lem5324317 s t l m h1)). Qed.
Lemma lem5324384 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5324385 (l : real) (m : real) : term206 l m.
Proof. exact (@lem5324384 term78 (term142 l m)). Qed.
Lemma lem5324386 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term207 l m.
Proof. exact (@lem5324385 l m (@lem5324382 s t l m h1)). Qed.
Lemma lem5324387 (l : real) (m : real) : (term208 l m) = (term142 l m).
Proof. exact (@lem1982733 (term142 l m)). Qed.
Lemma lem5324388 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5324389 (l : real) (m : real) : (term209 l m) = (term144 l m).
Proof. exact (MK_COMB (@lem5324388) (@lem5324387 l m)). Qed.
Lemma lem5324390 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324391 (l : real) (m : real) : (term207 l m) = (term145 l m).
Proof. exact (MK_COMB (@lem5324389 l m) (@lem5324390)). Qed.
Lemma lem5324392 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term145 l m.
Proof. exact (EQ_MP (@lem5324391 l m) (@lem5324386 s t l m h1)). Qed.
Lemma lem5324394 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5324395 : term210 = term211.
Proof. exact (@lem5324394 term43 term54). Qed.
Lemma lem5324396 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem5324398 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324399 : term43 = term194.
Proof. exact (@lem5324398 (NUMERAL 0)). Qed.
Lemma lem5324400 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324401 : term195 = term196.
Proof. exact (MK_COMB (@lem5324400) (@lem5324399)). Qed.
Lemma lem5324402 : term211 = term212.
Proof. exact (MK_COMB (@lem5324401) (@lem5324396)). Qed.
Lemma lem5324403 : term213.
Proof. exact (@lem1980255 term43 term50 term78 term78). Qed.
Lemma lem5324405 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324406 : term117 = term118.
Proof. exact (@lem5324405 (NUMERAL 0) term72). Qed.
Lemma lem5324407 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324408 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324409 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324408 h1) (fun h1 : term118 = True => @lem5324407)). Qed.
Lemma lem5324410 : term118 = True.
Proof. exact (EQ_MP (@lem5324409) (@lem5324407)). Qed.
Lemma lem5324411 : term117 = True.
Proof. exact (TRANS (@lem5324406) (@lem5324410)). Qed.
Lemma lem5324412 : True = term117.
Proof. exact (SYM (@lem5324411)). Qed.
Lemma lem5324413 : term117.
Proof. exact (EQ_MP (@lem5324412) (@lem0)). Qed.
Lemma lem5324414 : term214.
Proof. exact (@lem5324403 (@lem5324413)). Qed.
Lemma lem5324416 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324417 : term113 = term114.
Proof. exact (@lem5324416 (NUMERAL 0) term55). Qed.
Lemma lem5324418 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324419 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324420 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324419 h1) (fun h1 : term114 = True => @lem5324418)). Qed.
Lemma lem5324421 : term114 = True.
Proof. exact (EQ_MP (@lem5324420) (@lem5324418)). Qed.
Lemma lem5324422 : term113 = True.
Proof. exact (TRANS (@lem5324417) (@lem5324421)). Qed.
Lemma lem5324423 : True = term113.
Proof. exact (SYM (@lem5324422)). Qed.
Lemma lem5324424 : term113.
Proof. exact (EQ_MP (@lem5324423) (@lem0)). Qed.
Lemma lem5324425 : term212 = term215.
Proof. exact (@lem5324414 (@lem5324424)). Qed.
Lemma lem5324427 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324428 : term166 = term92.
Proof. exact (@lem5324427 term72 term72). Qed.
Lemma lem5324429 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324430 : term91 = term72.
Proof. exact (EQ_MP (@lem5324429) (@lem940073)). Qed.
Lemma lem5324431 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324432 : term92 = term78.
Proof. exact (MK_COMB (@lem5324431) (@lem5324430)). Qed.
Lemma lem5324433 : term166 = term78.
Proof. exact (TRANS (@lem5324428) (@lem5324432)). Qed.
Lemma lem5324435 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324436 : term216 = term43.
Proof. exact (@lem5324435 term55). Qed.
Lemma lem5324437 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324438 : term217 = term195.
Proof. exact (MK_COMB (@lem5324437) (@lem5324436)). Qed.
Lemma lem5324439 : term215 = term117.
Proof. exact (MK_COMB (@lem5324438) (@lem5324433)). Qed.
Lemma lem5324441 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324442 : term117 = term118.
Proof. exact (@lem5324441 (NUMERAL 0) term72). Qed.
Lemma lem5324443 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324444 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324445 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324444 h1) (fun h1 : term118 = True => @lem5324443)). Qed.
Lemma lem5324446 : term118 = True.
Proof. exact (EQ_MP (@lem5324445) (@lem5324443)). Qed.
Lemma lem5324447 : term117 = True.
Proof. exact (TRANS (@lem5324442) (@lem5324446)). Qed.
Lemma lem5324448 : term215 = True.
Proof. exact (TRANS (@lem5324439) (@lem5324447)). Qed.
Lemma lem5324449 : term212 = True.
Proof. exact (TRANS (@lem5324425) (@lem5324448)). Qed.
Lemma lem5324450 : term211 = True.
Proof. exact (TRANS (@lem5324402) (@lem5324449)). Qed.
Lemma lem5324451 : term210 = True.
Proof. exact (TRANS (@lem5324395) (@lem5324450)). Qed.
Lemma lem5324452 : True = term210.
Proof. exact (SYM (@lem5324451)). Qed.
Lemma lem5324453 : term210.
Proof. exact (EQ_MP (@lem5324452) (@lem0)). Qed.
Lemma lem5324454 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term218 l m.
Proof. exact (conj (@lem5324453) (@lem5324318 s t l m h1)). Qed.
Lemma lem5324456 (x : real) (y : real) : term219 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5324457 (l : real) (m : real) : term220 l m.
Proof. exact (@lem5324456 term54 (term39 l m)). Qed.
Lemma lem5324458 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term221 l m.
Proof. exact (@lem5324457 l m (@lem5324454 s t l m h1)). Qed.
Lemma lem5324459 (l : real) (m : real) : (term222 l m) = (term223 l m).
Proof. exact (@lem1982781 (term40 l) term54 m). Qed.
Lemma lem5324460 (m : real) : (term65 m) = (term65 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem5324461 (l : real) : (term224 l) = (term225 l).
Proof. exact (@lem1982749 term54 term66 l). Qed.
Lemma lem5324463 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5324464 : term66 = term71.
Proof. exact (@lem5324463 term72). Qed.
Lemma lem5324467 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem5324468 : term226 = term227.
Proof. exact (MK_COMB (@lem5324467) (@lem5324464)). Qed.
Lemma lem5324469 : term227 = term228.
Proof. exact (@lem1981613 term78 term66 term50 term78). Qed.
Lemma lem5324471 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324472 : term133 = term134.
Proof. exact (@lem5324471 term55 term72). Qed.
Lemma lem5324473 : term135 = term84.
Proof. exact (@lem996237 term84). Qed.
Lemma lem5324474 : (term135 = term84) = (term136 = term55).
Proof. exact (@lem1007663 term84 (BIT1 0) term84). Qed.
Lemma lem5324475 : term136 = term55.
Proof. exact (EQ_MP (@lem5324474) (@lem5324473)). Qed.
Lemma lem5324476 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324477 : term134 = term50.
Proof. exact (MK_COMB (@lem5324476) (@lem5324475)). Qed.
Lemma lem5324478 : term133 = term50.
Proof. exact (TRANS (@lem5324472) (@lem5324477)). Qed.
Lemma lem5324480 (m : nat) (n : nat) : (term229 m n) = (term87 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5324481 : term230 = term89.
Proof. exact (@lem5324480 term72 term72). Qed.
Lemma lem5324482 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324483 : term91 = term72.
Proof. exact (EQ_MP (@lem5324482) (@lem940073)). Qed.
Lemma lem5324484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324485 : term92 = term78.
Proof. exact (MK_COMB (@lem5324484) (@lem5324483)). Qed.
Lemma lem5324486 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324487 : term89 = term66.
Proof. exact (MK_COMB (@lem5324486) (@lem5324485)). Qed.
Lemma lem5324488 : term230 = term66.
Proof. exact (TRANS (@lem5324481) (@lem5324487)). Qed.
Lemma lem5324489 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5324490 : term231 = term94.
Proof. exact (MK_COMB (@lem5324489) (@lem5324488)). Qed.
Lemma lem5324491 : term228 = term95.
Proof. exact (MK_COMB (@lem5324490) (@lem5324478)). Qed.
Lemma lem5324492 : term227 = term95.
Proof. exact (TRANS (@lem5324469) (@lem5324491)). Qed.
Lemma lem5324495 : term226 = term95.
Proof. exact (TRANS (@lem5324468) (@lem5324492)). Qed.
Lemma lem5324496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324497 : term232 = term97.
Proof. exact (MK_COMB (@lem5324496) (@lem5324495)). Qed.
Lemma lem5324498 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5324499 (l : real) : (term225 l) = (term98 l).
Proof. exact (MK_COMB (@lem5324497) (@lem5324498 l)). Qed.
Lemma lem5324500 (l : real) : (term224 l) = (term98 l).
Proof. exact (TRANS (@lem5324461 l) (@lem5324499 l)). Qed.
Lemma lem5324501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324502 (l : real) : (term233 l) = (term100 l).
Proof. exact (MK_COMB (@lem5324501) (@lem5324500 l)). Qed.
Lemma lem5324503 (l : real) (m : real) : (term223 l m) = (term234 l m).
Proof. exact (MK_COMB (@lem5324502 l) (@lem5324460 m)). Qed.
Lemma lem5324504 (l : real) (m : real) : (term222 l m) = (term234 l m).
Proof. exact (TRANS (@lem5324459 l m) (@lem5324503 l m)). Qed.
Lemma lem5324505 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5324506 (l : real) (m : real) : (term235 l m) = (term236 l m).
Proof. exact (MK_COMB (@lem5324505) (@lem5324504 l m)). Qed.
Lemma lem5324507 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324508 (l : real) (m : real) : (term221 l m) = (term237 l m).
Proof. exact (MK_COMB (@lem5324506 l m) (@lem5324507)). Qed.
Lemma lem5324509 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term237 l m.
Proof. exact (EQ_MP (@lem5324508 l m) (@lem5324458 s t l m h1)). Qed.
Lemma lem5324510 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term238 l m.
Proof. exact (conj (@lem5324509 s t l m h1) (@lem5324392 s t l m h1)). Qed.
Lemma lem5324512 (x : real) (y : real) : term239 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5324513 (l : real) (m : real) : term240 l m.
Proof. exact (@lem5324512 (term234 l m) (term142 l m)). Qed.
Lemma lem5324514 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term241 l m.
Proof. exact (@lem5324513 l m (@lem5324510 s t l m h1)). Qed.
Lemma lem5324515 (l : real) (m : real) : (term242 l m) = (term243 l m).
Proof. exact (@lem1982753 (term98 l) (term65 l) (term65 m) (term98 m)). Qed.
Lemma lem5324516 (l : real) : (term244 l) = (term245 l).
Proof. exact (@lem1982711 term95 term54 l). Qed.
Lemma lem5324522 : term246.
Proof. exact (@lem1981473 term66 term50 term78 term50 term43 term78). Qed.
Lemma lem5324524 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324525 : term113 = term114.
Proof. exact (@lem5324524 (NUMERAL 0) term55). Qed.
Lemma lem5324526 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324527 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324528 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324527 h1) (fun h1 : term114 = True => @lem5324526)). Qed.
Lemma lem5324529 : term114 = True.
Proof. exact (EQ_MP (@lem5324528) (@lem5324526)). Qed.
Lemma lem5324530 : term113 = True.
Proof. exact (TRANS (@lem5324525) (@lem5324529)). Qed.
Lemma lem5324531 : True = term113.
Proof. exact (SYM (@lem5324530)). Qed.
Lemma lem5324532 : term113.
Proof. exact (EQ_MP (@lem5324531) (@lem0)). Qed.
Lemma lem5324533 : term247.
Proof. exact (@lem5324522 (@lem5324532)). Qed.
Lemma lem5324535 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324536 : term113 = term114.
Proof. exact (@lem5324535 (NUMERAL 0) term55). Qed.
Lemma lem5324537 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324538 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324539 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324538 h1) (fun h1 : term114 = True => @lem5324537)). Qed.
Lemma lem5324540 : term114 = True.
Proof. exact (EQ_MP (@lem5324539) (@lem5324537)). Qed.
Lemma lem5324541 : term113 = True.
Proof. exact (TRANS (@lem5324536) (@lem5324540)). Qed.
Lemma lem5324542 : True = term113.
Proof. exact (SYM (@lem5324541)). Qed.
Lemma lem5324543 : term113.
Proof. exact (EQ_MP (@lem5324542) (@lem0)). Qed.
Lemma lem5324544 : term248.
Proof. exact (@lem5324533 (@lem5324543)). Qed.
Lemma lem5324546 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324547 : term117 = term118.
Proof. exact (@lem5324546 (NUMERAL 0) term72). Qed.
Lemma lem5324548 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324549 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324550 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324549 h1) (fun h1 : term118 = True => @lem5324548)). Qed.
Lemma lem5324551 : term118 = True.
Proof. exact (EQ_MP (@lem5324550) (@lem5324548)). Qed.
Lemma lem5324552 : term117 = True.
Proof. exact (TRANS (@lem5324547) (@lem5324551)). Qed.
Lemma lem5324553 : True = term117.
Proof. exact (SYM (@lem5324552)). Qed.
Lemma lem5324554 : term117.
Proof. exact (EQ_MP (@lem5324553) (@lem0)). Qed.
Lemma lem5324555 : term249.
Proof. exact (@lem5324544 (@lem5324554)). Qed.
Lemma lem5324557 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324558 : term81 = term82.
Proof. exact (@lem5324557 term72 term55). Qed.
Lemma lem5324559 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324560 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324561 : term85 = term55.
Proof. exact (EQ_MP (@lem5324560) (@lem5324559)). Qed.
Lemma lem5324562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324563 : term82 = term50.
Proof. exact (MK_COMB (@lem5324562) (@lem5324561)). Qed.
Lemma lem5324564 : term81 = term50.
Proof. exact (TRANS (@lem5324558) (@lem5324563)). Qed.
Lemma lem5324566 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5324567 : term163 = term164.
Proof. exact (@lem5324566 term72 term55). Qed.
Lemma lem5324568 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324569 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324570 : term85 = term55.
Proof. exact (EQ_MP (@lem5324569) (@lem5324568)). Qed.
Lemma lem5324571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324572 : term82 = term50.
Proof. exact (MK_COMB (@lem5324571) (@lem5324570)). Qed.
Lemma lem5324573 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324574 : term164 = term165.
Proof. exact (MK_COMB (@lem5324573) (@lem5324572)). Qed.
Lemma lem5324575 : term163 = term165.
Proof. exact (TRANS (@lem5324567) (@lem5324574)). Qed.
Lemma lem5324576 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324577 : term250 = term251.
Proof. exact (MK_COMB (@lem5324576) (@lem5324575)). Qed.
Lemma lem5324578 : term252 = term253.
Proof. exact (MK_COMB (@lem5324577) (@lem5324564)). Qed.
Lemma lem5324580 (m : nat) : (term254 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5324581 : term253 = term43.
Proof. exact (@lem5324580 term55). Qed.
Lemma lem5324582 : term252 = term43.
Proof. exact (TRANS (@lem5324578) (@lem5324581)). Qed.
Lemma lem5324583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324584 : term255 = term256.
Proof. exact (MK_COMB (@lem5324583) (@lem5324582)). Qed.
Lemma lem5324585 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5324586 : term257 = term202.
Proof. exact (MK_COMB (@lem5324584) (@lem5324585)). Qed.
Lemma lem5324588 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324589 : term202 = term43.
Proof. exact (@lem5324588 term72). Qed.
Lemma lem5324590 : term257 = term43.
Proof. exact (TRANS (@lem5324586) (@lem5324589)). Qed.
Lemma lem5324592 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324593 : term258 = term259.
Proof. exact (@lem5324592 term55 term55). Qed.
Lemma lem5324594 : (term90 = (BIT1 0)) = (term260 = term261).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324595 : term260 = term261.
Proof. exact (EQ_MP (@lem5324594) (@lem940073)). Qed.
Lemma lem5324596 : (term260 = term261) = (term262 = term263).
Proof. exact (@lem1008952 term84 term261). Qed.
Lemma lem5324597 : term262 = term263.
Proof. exact (EQ_MP (@lem5324596) (@lem5324595)). Qed.
Lemma lem5324598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324599 : term259 = term264.
Proof. exact (MK_COMB (@lem5324598) (@lem5324597)). Qed.
Lemma lem5324600 : term258 = term264.
Proof. exact (TRANS (@lem5324593) (@lem5324599)). Qed.
Lemma lem5324601 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5324602 : term265 = term266.
Proof. exact (MK_COMB (@lem5324601) (@lem5324600)). Qed.
Lemma lem5324604 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324605 : term266 = term43.
Proof. exact (@lem5324604 term263). Qed.
Lemma lem5324606 : term265 = term43.
Proof. exact (TRANS (@lem5324602) (@lem5324605)). Qed.
Lemma lem5324607 : term43 = term265.
Proof. exact (SYM (@lem5324606)). Qed.
Lemma lem5324608 : term257 = term265.
Proof. exact (TRANS (@lem5324590) (@lem5324607)). Qed.
Lemma lem5324610 : term267 = term194.
Proof. exact (@lem5324555 (@lem5324608)). Qed.
Lemma lem5324612 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5324613 : term194 = term43.
Proof. exact (@lem5324612 term43). Qed.
Lemma lem5324614 : term267 = term43.
Proof. exact (TRANS (@lem5324610) (@lem5324613)). Qed.
Lemma lem5324615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324616 : term269 = term256.
Proof. exact (MK_COMB (@lem5324615) (@lem5324614)). Qed.
Lemma lem5324617 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5324618 (l : real) : (term245 l) = (term270 l).
Proof. exact (MK_COMB (@lem5324616) (@lem5324617 l)). Qed.
Lemma lem5324619 (l : real) : (term244 l) = (term270 l).
Proof. exact (TRANS (@lem5324516 l) (@lem5324618 l)). Qed.
Lemma lem5324620 (l : real) : (term270 l) = term43.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5324621 (l : real) : (term244 l) = term43.
Proof. exact (TRANS (@lem5324619 l) (@lem5324620 l)). Qed.
Lemma lem5324622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324623 (l : real) : (term271 l) = term272.
Proof. exact (MK_COMB (@lem5324622) (@lem5324621 l)). Qed.
Lemma lem5324624 (m : real) : (term273 m) = (term274 m).
Proof. exact (@lem1982711 term54 term95 m). Qed.
Lemma lem5324630 : term275.
Proof. exact (@lem1981473 term78 term50 term66 term50 term43 term78). Qed.
Lemma lem5324632 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324633 : term113 = term114.
Proof. exact (@lem5324632 (NUMERAL 0) term55). Qed.
Lemma lem5324634 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324635 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324636 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324635 h1) (fun h1 : term114 = True => @lem5324634)). Qed.
Lemma lem5324637 : term114 = True.
Proof. exact (EQ_MP (@lem5324636) (@lem5324634)). Qed.
Lemma lem5324638 : term113 = True.
Proof. exact (TRANS (@lem5324633) (@lem5324637)). Qed.
Lemma lem5324639 : True = term113.
Proof. exact (SYM (@lem5324638)). Qed.
Lemma lem5324640 : term113.
Proof. exact (EQ_MP (@lem5324639) (@lem0)). Qed.
Lemma lem5324641 : term276.
Proof. exact (@lem5324630 (@lem5324640)). Qed.
Lemma lem5324643 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324644 : term113 = term114.
Proof. exact (@lem5324643 (NUMERAL 0) term55). Qed.
Lemma lem5324645 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324646 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324647 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324646 h1) (fun h1 : term114 = True => @lem5324645)). Qed.
Lemma lem5324648 : term114 = True.
Proof. exact (EQ_MP (@lem5324647) (@lem5324645)). Qed.
Lemma lem5324649 : term113 = True.
Proof. exact (TRANS (@lem5324644) (@lem5324648)). Qed.
Lemma lem5324650 : True = term113.
Proof. exact (SYM (@lem5324649)). Qed.
Lemma lem5324651 : term113.
Proof. exact (EQ_MP (@lem5324650) (@lem0)). Qed.
Lemma lem5324652 : term277.
Proof. exact (@lem5324641 (@lem5324651)). Qed.
Lemma lem5324654 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324655 : term117 = term118.
Proof. exact (@lem5324654 (NUMERAL 0) term72). Qed.
Lemma lem5324656 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324657 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324658 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324657 h1) (fun h1 : term118 = True => @lem5324656)). Qed.
Lemma lem5324659 : term118 = True.
Proof. exact (EQ_MP (@lem5324658) (@lem5324656)). Qed.
Lemma lem5324660 : term117 = True.
Proof. exact (TRANS (@lem5324655) (@lem5324659)). Qed.
Lemma lem5324661 : True = term117.
Proof. exact (SYM (@lem5324660)). Qed.
Lemma lem5324662 : term117.
Proof. exact (EQ_MP (@lem5324661) (@lem0)). Qed.
Lemma lem5324663 : term278.
Proof. exact (@lem5324652 (@lem5324662)). Qed.
Lemma lem5324665 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5324666 : term163 = term164.
Proof. exact (@lem5324665 term72 term55). Qed.
Lemma lem5324667 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324668 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324669 : term85 = term55.
Proof. exact (EQ_MP (@lem5324668) (@lem5324667)). Qed.
Lemma lem5324670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324671 : term82 = term50.
Proof. exact (MK_COMB (@lem5324670) (@lem5324669)). Qed.
Lemma lem5324672 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324673 : term164 = term165.
Proof. exact (MK_COMB (@lem5324672) (@lem5324671)). Qed.
Lemma lem5324674 : term163 = term165.
Proof. exact (TRANS (@lem5324666) (@lem5324673)). Qed.
Lemma lem5324676 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324677 : term81 = term82.
Proof. exact (@lem5324676 term72 term55). Qed.
Lemma lem5324678 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5324679 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5324680 : term85 = term55.
Proof. exact (EQ_MP (@lem5324679) (@lem5324678)). Qed.
Lemma lem5324681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324682 : term82 = term50.
Proof. exact (MK_COMB (@lem5324681) (@lem5324680)). Qed.
Lemma lem5324683 : term81 = term50.
Proof. exact (TRANS (@lem5324677) (@lem5324682)). Qed.
Lemma lem5324684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324685 : term279 = term280.
Proof. exact (MK_COMB (@lem5324684) (@lem5324683)). Qed.
Lemma lem5324686 : term281 = term282.
Proof. exact (MK_COMB (@lem5324685) (@lem5324674)). Qed.
Lemma lem5324688 (m : nat) : (term283 m) = term43.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5324689 : term282 = term43.
Proof. exact (@lem5324688 term55). Qed.
Lemma lem5324690 : term281 = term43.
Proof. exact (TRANS (@lem5324686) (@lem5324689)). Qed.
Lemma lem5324691 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324692 : term284 = term256.
Proof. exact (MK_COMB (@lem5324691) (@lem5324690)). Qed.
Lemma lem5324693 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5324694 : term285 = term202.
Proof. exact (MK_COMB (@lem5324692) (@lem5324693)). Qed.
Lemma lem5324696 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324697 : term202 = term43.
Proof. exact (@lem5324696 term72). Qed.
Lemma lem5324698 : term285 = term43.
Proof. exact (TRANS (@lem5324694) (@lem5324697)). Qed.
Lemma lem5324700 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324701 : term258 = term259.
Proof. exact (@lem5324700 term55 term55). Qed.
Lemma lem5324702 : (term90 = (BIT1 0)) = (term260 = term261).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324703 : term260 = term261.
Proof. exact (EQ_MP (@lem5324702) (@lem940073)). Qed.
Lemma lem5324704 : (term260 = term261) = (term262 = term263).
Proof. exact (@lem1008952 term84 term261). Qed.
Lemma lem5324705 : term262 = term263.
Proof. exact (EQ_MP (@lem5324704) (@lem5324703)). Qed.
Lemma lem5324706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324707 : term259 = term264.
Proof. exact (MK_COMB (@lem5324706) (@lem5324705)). Qed.
Lemma lem5324708 : term258 = term264.
Proof. exact (TRANS (@lem5324701) (@lem5324707)). Qed.
Lemma lem5324709 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5324710 : term265 = term266.
Proof. exact (MK_COMB (@lem5324709) (@lem5324708)). Qed.
Lemma lem5324712 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324713 : term266 = term43.
Proof. exact (@lem5324712 term263). Qed.
Lemma lem5324714 : term265 = term43.
Proof. exact (TRANS (@lem5324710) (@lem5324713)). Qed.
Lemma lem5324715 : term43 = term265.
Proof. exact (SYM (@lem5324714)). Qed.
Lemma lem5324716 : term285 = term265.
Proof. exact (TRANS (@lem5324698) (@lem5324715)). Qed.
Lemma lem5324718 : term286 = term194.
Proof. exact (@lem5324663 (@lem5324716)). Qed.
Lemma lem5324720 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5324721 : term194 = term43.
Proof. exact (@lem5324720 term43). Qed.
Lemma lem5324722 : term286 = term43.
Proof. exact (TRANS (@lem5324718) (@lem5324721)). Qed.
Lemma lem5324723 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324724 : term287 = term256.
Proof. exact (MK_COMB (@lem5324723) (@lem5324722)). Qed.
Lemma lem5324725 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5324726 (m : real) : (term274 m) = (term270 m).
Proof. exact (MK_COMB (@lem5324724) (@lem5324725 m)). Qed.
Lemma lem5324727 (m : real) : (term273 m) = (term270 m).
Proof. exact (TRANS (@lem5324624 m) (@lem5324726 m)). Qed.
Lemma lem5324728 (m : real) : (term270 m) = term43.
Proof. exact (@lem1982719 m). Qed.
Lemma lem5324729 (m : real) : (term273 m) = term43.
Proof. exact (TRANS (@lem5324727 m) (@lem5324728 m)). Qed.
Lemma lem5324730 (l : real) (m : real) : (term243 l m) = term288.
Proof. exact (MK_COMB (@lem5324623 l) (@lem5324729 m)). Qed.
Lemma lem5324731 (l : real) (m : real) : (term242 l m) = term288.
Proof. exact (TRANS (@lem5324515 l m) (@lem5324730 l m)). Qed.
Lemma lem5324732 : term288 = term43.
Proof. exact (@lem1982721 term43). Qed.
Lemma lem5324733 (l : real) (m : real) : (term242 l m) = term43.
Proof. exact (TRANS (@lem5324731 l m) (@lem5324732)). Qed.
Lemma lem5324734 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5324735 (l : real) (m : real) : (term289 l m) = term290.
Proof. exact (MK_COMB (@lem5324734) (@lem5324733 l m)). Qed.
Lemma lem5324736 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324737 (l : real) (m : real) : (term241 l m) = term291.
Proof. exact (MK_COMB (@lem5324735 l m) (@lem5324736)). Qed.
Lemma lem5324738 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term291.
Proof. exact (EQ_MP (@lem5324737 l m) (@lem5324514 s t l m h1)). Qed.
Lemma lem5324740 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5324741 : term291 = term292.
Proof. exact (@lem5324740 term43 term43). Qed.
Lemma lem5324743 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324744 : term43 = term194.
Proof. exact (@lem5324743 (NUMERAL 0)). Qed.
Lemma lem5324746 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324747 : term43 = term194.
Proof. exact (@lem5324746 (NUMERAL 0)). Qed.
Lemma lem5324748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324749 : term195 = term196.
Proof. exact (MK_COMB (@lem5324748) (@lem5324747)). Qed.
Lemma lem5324750 : term292 = term293.
Proof. exact (MK_COMB (@lem5324749) (@lem5324744)). Qed.
Lemma lem5324751 : term294.
Proof. exact (@lem1980255 term43 term78 term43 term78). Qed.
Lemma lem5324753 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324754 : term117 = term118.
Proof. exact (@lem5324753 (NUMERAL 0) term72). Qed.
Lemma lem5324755 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324756 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324757 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324756 h1) (fun h1 : term118 = True => @lem5324755)). Qed.
Lemma lem5324758 : term118 = True.
Proof. exact (EQ_MP (@lem5324757) (@lem5324755)). Qed.
Lemma lem5324759 : term117 = True.
Proof. exact (TRANS (@lem5324754) (@lem5324758)). Qed.
Lemma lem5324760 : True = term117.
Proof. exact (SYM (@lem5324759)). Qed.
Lemma lem5324761 : term117.
Proof. exact (EQ_MP (@lem5324760) (@lem0)). Qed.
Lemma lem5324762 : term295.
Proof. exact (@lem5324751 (@lem5324761)). Qed.
Lemma lem5324764 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324765 : term117 = term118.
Proof. exact (@lem5324764 (NUMERAL 0) term72). Qed.
Lemma lem5324766 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324767 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324768 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324767 h1) (fun h1 : term118 = True => @lem5324766)). Qed.
Lemma lem5324769 : term118 = True.
Proof. exact (EQ_MP (@lem5324768) (@lem5324766)). Qed.
Lemma lem5324770 : term117 = True.
Proof. exact (TRANS (@lem5324765) (@lem5324769)). Qed.
Lemma lem5324771 : True = term117.
Proof. exact (SYM (@lem5324770)). Qed.
Lemma lem5324772 : term117.
Proof. exact (EQ_MP (@lem5324771) (@lem0)). Qed.
Lemma lem5324773 : term293 = term296.
Proof. exact (@lem5324762 (@lem5324772)). Qed.
Lemma lem5324775 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324776 : term202 = term43.
Proof. exact (@lem5324775 term72). Qed.
Lemma lem5324778 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324779 : term202 = term43.
Proof. exact (@lem5324778 term72). Qed.
Lemma lem5324780 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324781 : term203 = term195.
Proof. exact (MK_COMB (@lem5324780) (@lem5324779)). Qed.
Lemma lem5324782 : term296 = term292.
Proof. exact (MK_COMB (@lem5324781) (@lem5324776)). Qed.
Lemma lem5324784 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324785 : term292 = term297.
Proof. exact (@lem5324784 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5324786 : term297 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5324787 : term292 = False.
Proof. exact (TRANS (@lem5324785) (@lem5324786)). Qed.
Lemma lem5324788 : term296 = False.
Proof. exact (TRANS (@lem5324782) (@lem5324787)). Qed.
Lemma lem5324789 : term293 = False.
Proof. exact (TRANS (@lem5324773) (@lem5324788)). Qed.
Lemma lem5324790 : term292 = False.
Proof. exact (TRANS (@lem5324750) (@lem5324789)). Qed.
Lemma lem5324791 : term291 = False.
Proof. exact (TRANS (@lem5324741) (@lem5324790)). Qed.
Lemma lem5324792 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : False.
Proof. exact (EQ_MP (@lem5324791) (@lem5324738 s t l m h1)). Qed.
Lemma lem5324793 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term192 s t l m.
Proof. exact (h1). Qed.
Lemma lem5324794 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term191 t l m.
Proof. exact (proj2 (@lem5324793 s t l m h1)). Qed.
Lemma lem5324796 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term188 l m.
Proof. exact (proj2 (@lem5324794 s t l m h1)). Qed.
Lemma lem5324798 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term145 l m.
Proof. exact (proj2 (@lem5324796 s t l m h1)). Qed.
Lemma lem5324799 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term44 l m.
Proof. exact (proj1 (@lem5324796 s t l m h1)). Qed.
Lemma lem5324801 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5324802 : term193 = term117.
Proof. exact (@lem5324801 term43 term78). Qed.
Lemma lem5324804 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324805 : term78 = term107.
Proof. exact (@lem5324804 term72). Qed.
Lemma lem5324807 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324808 : term43 = term194.
Proof. exact (@lem5324807 (NUMERAL 0)). Qed.
Lemma lem5324809 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324810 : term195 = term196.
Proof. exact (MK_COMB (@lem5324809) (@lem5324808)). Qed.
Lemma lem5324811 : term117 = term197.
Proof. exact (MK_COMB (@lem5324810) (@lem5324805)). Qed.
Lemma lem5324812 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5324814 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324815 : term117 = term118.
Proof. exact (@lem5324814 (NUMERAL 0) term72). Qed.
Lemma lem5324816 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324817 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324818 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324817 h1) (fun h1 : term118 = True => @lem5324816)). Qed.
Lemma lem5324819 : term118 = True.
Proof. exact (EQ_MP (@lem5324818) (@lem5324816)). Qed.
Lemma lem5324820 : term117 = True.
Proof. exact (TRANS (@lem5324815) (@lem5324819)). Qed.
Lemma lem5324821 : True = term117.
Proof. exact (SYM (@lem5324820)). Qed.
Lemma lem5324822 : term117.
Proof. exact (EQ_MP (@lem5324821) (@lem0)). Qed.
Lemma lem5324823 : term199.
Proof. exact (@lem5324812 (@lem5324822)). Qed.
Lemma lem5324825 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324826 : term117 = term118.
Proof. exact (@lem5324825 (NUMERAL 0) term72). Qed.
Lemma lem5324827 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324828 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324829 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324828 h1) (fun h1 : term118 = True => @lem5324827)). Qed.
Lemma lem5324830 : term118 = True.
Proof. exact (EQ_MP (@lem5324829) (@lem5324827)). Qed.
Lemma lem5324831 : term117 = True.
Proof. exact (TRANS (@lem5324826) (@lem5324830)). Qed.
Lemma lem5324832 : True = term117.
Proof. exact (SYM (@lem5324831)). Qed.
Lemma lem5324833 : term117.
Proof. exact (EQ_MP (@lem5324832) (@lem0)). Qed.
Lemma lem5324834 : term197 = term200.
Proof. exact (@lem5324823 (@lem5324833)). Qed.
Lemma lem5324836 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324837 : term166 = term92.
Proof. exact (@lem5324836 term72 term72). Qed.
Lemma lem5324838 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324839 : term91 = term72.
Proof. exact (EQ_MP (@lem5324838) (@lem940073)). Qed.
Lemma lem5324840 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324841 : term92 = term78.
Proof. exact (MK_COMB (@lem5324840) (@lem5324839)). Qed.
Lemma lem5324842 : term166 = term78.
Proof. exact (TRANS (@lem5324837) (@lem5324841)). Qed.
Lemma lem5324844 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324845 : term202 = term43.
Proof. exact (@lem5324844 term72). Qed.
Lemma lem5324846 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324847 : term203 = term195.
Proof. exact (MK_COMB (@lem5324846) (@lem5324845)). Qed.
Lemma lem5324848 : term200 = term117.
Proof. exact (MK_COMB (@lem5324847) (@lem5324842)). Qed.
Lemma lem5324850 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324851 : term117 = term118.
Proof. exact (@lem5324850 (NUMERAL 0) term72). Qed.
Lemma lem5324852 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324853 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324854 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324853 h1) (fun h1 : term118 = True => @lem5324852)). Qed.
Lemma lem5324855 : term118 = True.
Proof. exact (EQ_MP (@lem5324854) (@lem5324852)). Qed.
Lemma lem5324856 : term117 = True.
Proof. exact (TRANS (@lem5324851) (@lem5324855)). Qed.
Lemma lem5324857 : term200 = True.
Proof. exact (TRANS (@lem5324848) (@lem5324856)). Qed.
Lemma lem5324858 : term197 = True.
Proof. exact (TRANS (@lem5324834) (@lem5324857)). Qed.
Lemma lem5324859 : term117 = True.
Proof. exact (TRANS (@lem5324811) (@lem5324858)). Qed.
Lemma lem5324860 : term193 = True.
Proof. exact (TRANS (@lem5324802) (@lem5324859)). Qed.
Lemma lem5324861 : True = term193.
Proof. exact (SYM (@lem5324860)). Qed.
Lemma lem5324862 : term193.
Proof. exact (EQ_MP (@lem5324861) (@lem0)). Qed.
Lemma lem5324863 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term204 l m.
Proof. exact (conj (@lem5324862) (@lem5324798 s t l m h1)). Qed.
Lemma lem5324865 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5324866 (l : real) (m : real) : term206 l m.
Proof. exact (@lem5324865 term78 (term142 l m)). Qed.
Lemma lem5324867 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term207 l m.
Proof. exact (@lem5324866 l m (@lem5324863 s t l m h1)). Qed.
Lemma lem5324868 (l : real) (m : real) : (term208 l m) = (term142 l m).
Proof. exact (@lem1982733 (term142 l m)). Qed.
Lemma lem5324869 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5324870 (l : real) (m : real) : (term209 l m) = (term144 l m).
Proof. exact (MK_COMB (@lem5324869) (@lem5324868 l m)). Qed.
Lemma lem5324871 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324872 (l : real) (m : real) : (term207 l m) = (term145 l m).
Proof. exact (MK_COMB (@lem5324870 l m) (@lem5324871)). Qed.
Lemma lem5324873 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term145 l m.
Proof. exact (EQ_MP (@lem5324872 l m) (@lem5324867 s t l m h1)). Qed.
Lemma lem5324875 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5324876 : term210 = term211.
Proof. exact (@lem5324875 term43 term54). Qed.
Lemma lem5324877 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem5324879 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5324880 : term43 = term194.
Proof. exact (@lem5324879 (NUMERAL 0)). Qed.
Lemma lem5324881 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324882 : term195 = term196.
Proof. exact (MK_COMB (@lem5324881) (@lem5324880)). Qed.
Lemma lem5324883 : term211 = term212.
Proof. exact (MK_COMB (@lem5324882) (@lem5324877)). Qed.
Lemma lem5324884 : term213.
Proof. exact (@lem1980255 term43 term50 term78 term78). Qed.
Lemma lem5324886 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324887 : term117 = term118.
Proof. exact (@lem5324886 (NUMERAL 0) term72). Qed.
Lemma lem5324888 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324889 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324890 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324889 h1) (fun h1 : term118 = True => @lem5324888)). Qed.
Lemma lem5324891 : term118 = True.
Proof. exact (EQ_MP (@lem5324890) (@lem5324888)). Qed.
Lemma lem5324892 : term117 = True.
Proof. exact (TRANS (@lem5324887) (@lem5324891)). Qed.
Lemma lem5324893 : True = term117.
Proof. exact (SYM (@lem5324892)). Qed.
Lemma lem5324894 : term117.
Proof. exact (EQ_MP (@lem5324893) (@lem0)). Qed.
Lemma lem5324895 : term214.
Proof. exact (@lem5324884 (@lem5324894)). Qed.
Lemma lem5324897 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324898 : term113 = term114.
Proof. exact (@lem5324897 (NUMERAL 0) term55). Qed.
Lemma lem5324899 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5324900 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5324901 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5324900 h1) (fun h1 : term114 = True => @lem5324899)). Qed.
Lemma lem5324902 : term114 = True.
Proof. exact (EQ_MP (@lem5324901) (@lem5324899)). Qed.
Lemma lem5324903 : term113 = True.
Proof. exact (TRANS (@lem5324898) (@lem5324902)). Qed.
Lemma lem5324904 : True = term113.
Proof. exact (SYM (@lem5324903)). Qed.
Lemma lem5324905 : term113.
Proof. exact (EQ_MP (@lem5324904) (@lem0)). Qed.
Lemma lem5324906 : term212 = term215.
Proof. exact (@lem5324895 (@lem5324905)). Qed.
Lemma lem5324908 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324909 : term166 = term92.
Proof. exact (@lem5324908 term72 term72). Qed.
Lemma lem5324910 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324911 : term91 = term72.
Proof. exact (EQ_MP (@lem5324910) (@lem940073)). Qed.
Lemma lem5324912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324913 : term92 = term78.
Proof. exact (MK_COMB (@lem5324912) (@lem5324911)). Qed.
Lemma lem5324914 : term166 = term78.
Proof. exact (TRANS (@lem5324909) (@lem5324913)). Qed.
Lemma lem5324916 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5324917 : term216 = term43.
Proof. exact (@lem5324916 term55). Qed.
Lemma lem5324918 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5324919 : term217 = term195.
Proof. exact (MK_COMB (@lem5324918) (@lem5324917)). Qed.
Lemma lem5324920 : term215 = term117.
Proof. exact (MK_COMB (@lem5324919) (@lem5324914)). Qed.
Lemma lem5324922 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5324923 : term117 = term118.
Proof. exact (@lem5324922 (NUMERAL 0) term72). Qed.
Lemma lem5324924 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5324925 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5324926 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5324925 h1) (fun h1 : term118 = True => @lem5324924)). Qed.
Lemma lem5324927 : term118 = True.
Proof. exact (EQ_MP (@lem5324926) (@lem5324924)). Qed.
Lemma lem5324928 : term117 = True.
Proof. exact (TRANS (@lem5324923) (@lem5324927)). Qed.
Lemma lem5324929 : term215 = True.
Proof. exact (TRANS (@lem5324920) (@lem5324928)). Qed.
Lemma lem5324930 : term212 = True.
Proof. exact (TRANS (@lem5324906) (@lem5324929)). Qed.
Lemma lem5324931 : term211 = True.
Proof. exact (TRANS (@lem5324883) (@lem5324930)). Qed.
Lemma lem5324932 : term210 = True.
Proof. exact (TRANS (@lem5324876) (@lem5324931)). Qed.
Lemma lem5324933 : True = term210.
Proof. exact (SYM (@lem5324932)). Qed.
Lemma lem5324934 : term210.
Proof. exact (EQ_MP (@lem5324933) (@lem0)). Qed.
Lemma lem5324935 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term218 l m.
Proof. exact (conj (@lem5324934) (@lem5324799 s t l m h1)). Qed.
Lemma lem5324937 (x : real) (y : real) : term219 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5324938 (l : real) (m : real) : term220 l m.
Proof. exact (@lem5324937 term54 (term39 l m)). Qed.
Lemma lem5324939 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term221 l m.
Proof. exact (@lem5324938 l m (@lem5324935 s t l m h1)). Qed.
Lemma lem5324940 (l : real) (m : real) : (term222 l m) = (term223 l m).
Proof. exact (@lem1982781 (term40 l) term54 m). Qed.
Lemma lem5324941 (m : real) : (term65 m) = (term65 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem5324942 (l : real) : (term224 l) = (term225 l).
Proof. exact (@lem1982749 term54 term66 l). Qed.
Lemma lem5324944 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5324945 : term66 = term71.
Proof. exact (@lem5324944 term72). Qed.
Lemma lem5324948 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem5324949 : term226 = term227.
Proof. exact (MK_COMB (@lem5324948) (@lem5324945)). Qed.
Lemma lem5324950 : term227 = term228.
Proof. exact (@lem1981613 term78 term66 term50 term78). Qed.
Lemma lem5324952 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5324953 : term133 = term134.
Proof. exact (@lem5324952 term55 term72). Qed.
Lemma lem5324954 : term135 = term84.
Proof. exact (@lem996237 term84). Qed.
Lemma lem5324955 : (term135 = term84) = (term136 = term55).
Proof. exact (@lem1007663 term84 (BIT1 0) term84). Qed.
Lemma lem5324956 : term136 = term55.
Proof. exact (EQ_MP (@lem5324955) (@lem5324954)). Qed.
Lemma lem5324957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324958 : term134 = term50.
Proof. exact (MK_COMB (@lem5324957) (@lem5324956)). Qed.
Lemma lem5324959 : term133 = term50.
Proof. exact (TRANS (@lem5324953) (@lem5324958)). Qed.
Lemma lem5324961 (m : nat) (n : nat) : (term229 m n) = (term87 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5324962 : term230 = term89.
Proof. exact (@lem5324961 term72 term72). Qed.
Lemma lem5324963 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5324964 : term91 = term72.
Proof. exact (EQ_MP (@lem5324963) (@lem940073)). Qed.
Lemma lem5324965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5324966 : term92 = term78.
Proof. exact (MK_COMB (@lem5324965) (@lem5324964)). Qed.
Lemma lem5324967 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5324968 : term89 = term66.
Proof. exact (MK_COMB (@lem5324967) (@lem5324966)). Qed.
Lemma lem5324969 : term230 = term66.
Proof. exact (TRANS (@lem5324962) (@lem5324968)). Qed.
Lemma lem5324970 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5324971 : term231 = term94.
Proof. exact (MK_COMB (@lem5324970) (@lem5324969)). Qed.
Lemma lem5324972 : term228 = term95.
Proof. exact (MK_COMB (@lem5324971) (@lem5324959)). Qed.
Lemma lem5324973 : term227 = term95.
Proof. exact (TRANS (@lem5324950) (@lem5324972)). Qed.
Lemma lem5324976 : term226 = term95.
Proof. exact (TRANS (@lem5324949) (@lem5324973)). Qed.
Lemma lem5324977 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5324978 : term232 = term97.
Proof. exact (MK_COMB (@lem5324977) (@lem5324976)). Qed.
Lemma lem5324979 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5324980 (l : real) : (term225 l) = (term98 l).
Proof. exact (MK_COMB (@lem5324978) (@lem5324979 l)). Qed.
Lemma lem5324981 (l : real) : (term224 l) = (term98 l).
Proof. exact (TRANS (@lem5324942 l) (@lem5324980 l)). Qed.
Lemma lem5324982 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5324983 (l : real) : (term233 l) = (term100 l).
Proof. exact (MK_COMB (@lem5324982) (@lem5324981 l)). Qed.
Lemma lem5324984 (l : real) (m : real) : (term223 l m) = (term234 l m).
Proof. exact (MK_COMB (@lem5324983 l) (@lem5324941 m)). Qed.
Lemma lem5324985 (l : real) (m : real) : (term222 l m) = (term234 l m).
Proof. exact (TRANS (@lem5324940 l m) (@lem5324984 l m)). Qed.
Lemma lem5324986 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5324987 (l : real) (m : real) : (term235 l m) = (term236 l m).
Proof. exact (MK_COMB (@lem5324986) (@lem5324985 l m)). Qed.
Lemma lem5324988 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5324989 (l : real) (m : real) : (term221 l m) = (term237 l m).
Proof. exact (MK_COMB (@lem5324987 l m) (@lem5324988)). Qed.
Lemma lem5324990 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term237 l m.
Proof. exact (EQ_MP (@lem5324989 l m) (@lem5324939 s t l m h1)). Qed.
Lemma lem5324991 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term238 l m.
Proof. exact (conj (@lem5324990 s t l m h1) (@lem5324873 s t l m h1)). Qed.
Lemma lem5324993 (x : real) (y : real) : term239 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5324994 (l : real) (m : real) : term240 l m.
Proof. exact (@lem5324993 (term234 l m) (term142 l m)). Qed.
Lemma lem5324995 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term241 l m.
Proof. exact (@lem5324994 l m (@lem5324991 s t l m h1)). Qed.
Lemma lem5324996 (l : real) (m : real) : (term242 l m) = (term243 l m).
Proof. exact (@lem1982753 (term98 l) (term65 l) (term65 m) (term98 m)). Qed.
Lemma lem5324997 (l : real) : (term244 l) = (term245 l).
Proof. exact (@lem1982711 term95 term54 l). Qed.
Lemma lem5325003 : term246.
Proof. exact (@lem1981473 term66 term50 term78 term50 term43 term78). Qed.
Lemma lem5325005 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325006 : term113 = term114.
Proof. exact (@lem5325005 (NUMERAL 0) term55). Qed.
Lemma lem5325007 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5325008 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5325009 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5325008 h1) (fun h1 : term114 = True => @lem5325007)). Qed.
Lemma lem5325010 : term114 = True.
Proof. exact (EQ_MP (@lem5325009) (@lem5325007)). Qed.
Lemma lem5325011 : term113 = True.
Proof. exact (TRANS (@lem5325006) (@lem5325010)). Qed.
Lemma lem5325012 : True = term113.
Proof. exact (SYM (@lem5325011)). Qed.
Lemma lem5325013 : term113.
Proof. exact (EQ_MP (@lem5325012) (@lem0)). Qed.
Lemma lem5325014 : term247.
Proof. exact (@lem5325003 (@lem5325013)). Qed.
Lemma lem5325016 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325017 : term113 = term114.
Proof. exact (@lem5325016 (NUMERAL 0) term55). Qed.
Lemma lem5325018 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5325019 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5325020 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5325019 h1) (fun h1 : term114 = True => @lem5325018)). Qed.
Lemma lem5325021 : term114 = True.
Proof. exact (EQ_MP (@lem5325020) (@lem5325018)). Qed.
Lemma lem5325022 : term113 = True.
Proof. exact (TRANS (@lem5325017) (@lem5325021)). Qed.
Lemma lem5325023 : True = term113.
Proof. exact (SYM (@lem5325022)). Qed.
Lemma lem5325024 : term113.
Proof. exact (EQ_MP (@lem5325023) (@lem0)). Qed.
Lemma lem5325025 : term248.
Proof. exact (@lem5325014 (@lem5325024)). Qed.
Lemma lem5325027 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325028 : term117 = term118.
Proof. exact (@lem5325027 (NUMERAL 0) term72). Qed.
Lemma lem5325029 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5325030 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5325031 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5325030 h1) (fun h1 : term118 = True => @lem5325029)). Qed.
Lemma lem5325032 : term118 = True.
Proof. exact (EQ_MP (@lem5325031) (@lem5325029)). Qed.
Lemma lem5325033 : term117 = True.
Proof. exact (TRANS (@lem5325028) (@lem5325032)). Qed.
Lemma lem5325034 : True = term117.
Proof. exact (SYM (@lem5325033)). Qed.
Lemma lem5325035 : term117.
Proof. exact (EQ_MP (@lem5325034) (@lem0)). Qed.
Lemma lem5325036 : term249.
Proof. exact (@lem5325025 (@lem5325035)). Qed.
Lemma lem5325038 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5325039 : term81 = term82.
Proof. exact (@lem5325038 term72 term55). Qed.
Lemma lem5325040 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5325041 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5325042 : term85 = term55.
Proof. exact (EQ_MP (@lem5325041) (@lem5325040)). Qed.
Lemma lem5325043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5325044 : term82 = term50.
Proof. exact (MK_COMB (@lem5325043) (@lem5325042)). Qed.
Lemma lem5325045 : term81 = term50.
Proof. exact (TRANS (@lem5325039) (@lem5325044)). Qed.
Lemma lem5325047 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5325048 : term163 = term164.
Proof. exact (@lem5325047 term72 term55). Qed.
Lemma lem5325049 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5325050 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5325051 : term85 = term55.
Proof. exact (EQ_MP (@lem5325050) (@lem5325049)). Qed.
Lemma lem5325052 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5325053 : term82 = term50.
Proof. exact (MK_COMB (@lem5325052) (@lem5325051)). Qed.
Lemma lem5325054 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5325055 : term164 = term165.
Proof. exact (MK_COMB (@lem5325054) (@lem5325053)). Qed.
Lemma lem5325056 : term163 = term165.
Proof. exact (TRANS (@lem5325048) (@lem5325055)). Qed.
Lemma lem5325057 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5325058 : term250 = term251.
Proof. exact (MK_COMB (@lem5325057) (@lem5325056)). Qed.
Lemma lem5325059 : term252 = term253.
Proof. exact (MK_COMB (@lem5325058) (@lem5325045)). Qed.
Lemma lem5325061 (m : nat) : (term254 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5325062 : term253 = term43.
Proof. exact (@lem5325061 term55). Qed.
Lemma lem5325063 : term252 = term43.
Proof. exact (TRANS (@lem5325059) (@lem5325062)). Qed.
Lemma lem5325064 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5325065 : term255 = term256.
Proof. exact (MK_COMB (@lem5325064) (@lem5325063)). Qed.
Lemma lem5325066 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5325067 : term257 = term202.
Proof. exact (MK_COMB (@lem5325065) (@lem5325066)). Qed.
Lemma lem5325069 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5325070 : term202 = term43.
Proof. exact (@lem5325069 term72). Qed.
Lemma lem5325071 : term257 = term43.
Proof. exact (TRANS (@lem5325067) (@lem5325070)). Qed.
Lemma lem5325073 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5325074 : term258 = term259.
Proof. exact (@lem5325073 term55 term55). Qed.
Lemma lem5325075 : (term90 = (BIT1 0)) = (term260 = term261).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5325076 : term260 = term261.
Proof. exact (EQ_MP (@lem5325075) (@lem940073)). Qed.
Lemma lem5325077 : (term260 = term261) = (term262 = term263).
Proof. exact (@lem1008952 term84 term261). Qed.
Lemma lem5325078 : term262 = term263.
Proof. exact (EQ_MP (@lem5325077) (@lem5325076)). Qed.
Lemma lem5325079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5325080 : term259 = term264.
Proof. exact (MK_COMB (@lem5325079) (@lem5325078)). Qed.
Lemma lem5325081 : term258 = term264.
Proof. exact (TRANS (@lem5325074) (@lem5325080)). Qed.
Lemma lem5325082 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5325083 : term265 = term266.
Proof. exact (MK_COMB (@lem5325082) (@lem5325081)). Qed.
Lemma lem5325085 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5325086 : term266 = term43.
Proof. exact (@lem5325085 term263). Qed.
Lemma lem5325087 : term265 = term43.
Proof. exact (TRANS (@lem5325083) (@lem5325086)). Qed.
Lemma lem5325088 : term43 = term265.
Proof. exact (SYM (@lem5325087)). Qed.
Lemma lem5325089 : term257 = term265.
Proof. exact (TRANS (@lem5325071) (@lem5325088)). Qed.
Lemma lem5325091 : term267 = term194.
Proof. exact (@lem5325036 (@lem5325089)). Qed.
Lemma lem5325093 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5325094 : term194 = term43.
Proof. exact (@lem5325093 term43). Qed.
Lemma lem5325095 : term267 = term43.
Proof. exact (TRANS (@lem5325091) (@lem5325094)). Qed.
Lemma lem5325096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5325097 : term269 = term256.
Proof. exact (MK_COMB (@lem5325096) (@lem5325095)). Qed.
Lemma lem5325098 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5325099 (l : real) : (term245 l) = (term270 l).
Proof. exact (MK_COMB (@lem5325097) (@lem5325098 l)). Qed.
Lemma lem5325100 (l : real) : (term244 l) = (term270 l).
Proof. exact (TRANS (@lem5324997 l) (@lem5325099 l)). Qed.
Lemma lem5325101 (l : real) : (term270 l) = term43.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5325102 (l : real) : (term244 l) = term43.
Proof. exact (TRANS (@lem5325100 l) (@lem5325101 l)). Qed.
Lemma lem5325103 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5325104 (l : real) : (term271 l) = term272.
Proof. exact (MK_COMB (@lem5325103) (@lem5325102 l)). Qed.
Lemma lem5325105 (m : real) : (term273 m) = (term274 m).
Proof. exact (@lem1982711 term54 term95 m). Qed.
Lemma lem5325111 : term275.
Proof. exact (@lem1981473 term78 term50 term66 term50 term43 term78). Qed.
Lemma lem5325113 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325114 : term113 = term114.
Proof. exact (@lem5325113 (NUMERAL 0) term55). Qed.
Lemma lem5325115 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5325116 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5325117 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5325116 h1) (fun h1 : term114 = True => @lem5325115)). Qed.
Lemma lem5325118 : term114 = True.
Proof. exact (EQ_MP (@lem5325117) (@lem5325115)). Qed.
Lemma lem5325119 : term113 = True.
Proof. exact (TRANS (@lem5325114) (@lem5325118)). Qed.
Lemma lem5325120 : True = term113.
Proof. exact (SYM (@lem5325119)). Qed.
Lemma lem5325121 : term113.
Proof. exact (EQ_MP (@lem5325120) (@lem0)). Qed.
Lemma lem5325122 : term276.
Proof. exact (@lem5325111 (@lem5325121)). Qed.
Lemma lem5325124 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325125 : term113 = term114.
Proof. exact (@lem5325124 (NUMERAL 0) term55). Qed.
Lemma lem5325126 : term115 = term84.
Proof. exact (@lem912803). Qed.
Lemma lem5325127 (h1 : term115 = term84) : term114 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term84 h1). Qed.
Lemma lem5325128 : (term115 = term84) = (term114 = True).
Proof. exact (prop_ext (fun h1 : term115 = term84 => @lem5325127 h1) (fun h1 : term114 = True => @lem5325126)). Qed.
Lemma lem5325129 : term114 = True.
Proof. exact (EQ_MP (@lem5325128) (@lem5325126)). Qed.
Lemma lem5325130 : term113 = True.
Proof. exact (TRANS (@lem5325125) (@lem5325129)). Qed.
Lemma lem5325131 : True = term113.
Proof. exact (SYM (@lem5325130)). Qed.
Lemma lem5325132 : term113.
Proof. exact (EQ_MP (@lem5325131) (@lem0)). Qed.
Lemma lem5325133 : term277.
Proof. exact (@lem5325122 (@lem5325132)). Qed.
Lemma lem5325135 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325136 : term117 = term118.
Proof. exact (@lem5325135 (NUMERAL 0) term72). Qed.
Lemma lem5325137 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5325138 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5325139 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5325138 h1) (fun h1 : term118 = True => @lem5325137)). Qed.
Lemma lem5325140 : term118 = True.
Proof. exact (EQ_MP (@lem5325139) (@lem5325137)). Qed.
Lemma lem5325141 : term117 = True.
Proof. exact (TRANS (@lem5325136) (@lem5325140)). Qed.
Lemma lem5325142 : True = term117.
Proof. exact (SYM (@lem5325141)). Qed.
Lemma lem5325143 : term117.
Proof. exact (EQ_MP (@lem5325142) (@lem0)). Qed.
Lemma lem5325144 : term278.
Proof. exact (@lem5325133 (@lem5325143)). Qed.
Lemma lem5325146 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5325147 : term163 = term164.
Proof. exact (@lem5325146 term72 term55). Qed.
Lemma lem5325148 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5325149 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5325150 : term85 = term55.
Proof. exact (EQ_MP (@lem5325149) (@lem5325148)). Qed.
Lemma lem5325151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5325152 : term82 = term50.
Proof. exact (MK_COMB (@lem5325151) (@lem5325150)). Qed.
Lemma lem5325153 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5325154 : term164 = term165.
Proof. exact (MK_COMB (@lem5325153) (@lem5325152)). Qed.
Lemma lem5325155 : term163 = term165.
Proof. exact (TRANS (@lem5325147) (@lem5325154)). Qed.
Lemma lem5325157 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5325158 : term81 = term82.
Proof. exact (@lem5325157 term72 term55). Qed.
Lemma lem5325159 : term83 = term84.
Proof. exact (@lem996238 term84). Qed.
Lemma lem5325160 : (term83 = term84) = (term85 = term55).
Proof. exact (@lem1007663 (BIT1 0) term84 term84). Qed.
Lemma lem5325161 : term85 = term55.
Proof. exact (EQ_MP (@lem5325160) (@lem5325159)). Qed.
Lemma lem5325162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5325163 : term82 = term50.
Proof. exact (MK_COMB (@lem5325162) (@lem5325161)). Qed.
Lemma lem5325164 : term81 = term50.
Proof. exact (TRANS (@lem5325158) (@lem5325163)). Qed.
Lemma lem5325165 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5325166 : term279 = term280.
Proof. exact (MK_COMB (@lem5325165) (@lem5325164)). Qed.
Lemma lem5325167 : term281 = term282.
Proof. exact (MK_COMB (@lem5325166) (@lem5325155)). Qed.
Lemma lem5325169 (m : nat) : (term283 m) = term43.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5325170 : term282 = term43.
Proof. exact (@lem5325169 term55). Qed.
Lemma lem5325171 : term281 = term43.
Proof. exact (TRANS (@lem5325167) (@lem5325170)). Qed.
Lemma lem5325172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5325173 : term284 = term256.
Proof. exact (MK_COMB (@lem5325172) (@lem5325171)). Qed.
Lemma lem5325174 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5325175 : term285 = term202.
Proof. exact (MK_COMB (@lem5325173) (@lem5325174)). Qed.
Lemma lem5325177 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5325178 : term202 = term43.
Proof. exact (@lem5325177 term72). Qed.
Lemma lem5325179 : term285 = term43.
Proof. exact (TRANS (@lem5325175) (@lem5325178)). Qed.
Lemma lem5325181 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5325182 : term258 = term259.
Proof. exact (@lem5325181 term55 term55). Qed.
Lemma lem5325183 : (term90 = (BIT1 0)) = (term260 = term261).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5325184 : term260 = term261.
Proof. exact (EQ_MP (@lem5325183) (@lem940073)). Qed.
Lemma lem5325185 : (term260 = term261) = (term262 = term263).
Proof. exact (@lem1008952 term84 term261). Qed.
Lemma lem5325186 : term262 = term263.
Proof. exact (EQ_MP (@lem5325185) (@lem5325184)). Qed.
Lemma lem5325187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5325188 : term259 = term264.
Proof. exact (MK_COMB (@lem5325187) (@lem5325186)). Qed.
Lemma lem5325189 : term258 = term264.
Proof. exact (TRANS (@lem5325182) (@lem5325188)). Qed.
Lemma lem5325190 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5325191 : term265 = term266.
Proof. exact (MK_COMB (@lem5325190) (@lem5325189)). Qed.
Lemma lem5325193 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5325194 : term266 = term43.
Proof. exact (@lem5325193 term263). Qed.
Lemma lem5325195 : term265 = term43.
Proof. exact (TRANS (@lem5325191) (@lem5325194)). Qed.
Lemma lem5325196 : term43 = term265.
Proof. exact (SYM (@lem5325195)). Qed.
Lemma lem5325197 : term285 = term265.
Proof. exact (TRANS (@lem5325179) (@lem5325196)). Qed.
Lemma lem5325199 : term286 = term194.
Proof. exact (@lem5325144 (@lem5325197)). Qed.
Lemma lem5325201 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5325202 : term194 = term43.
Proof. exact (@lem5325201 term43). Qed.
Lemma lem5325203 : term286 = term43.
Proof. exact (TRANS (@lem5325199) (@lem5325202)). Qed.
Lemma lem5325204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5325205 : term287 = term256.
Proof. exact (MK_COMB (@lem5325204) (@lem5325203)). Qed.
Lemma lem5325206 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5325207 (m : real) : (term274 m) = (term270 m).
Proof. exact (MK_COMB (@lem5325205) (@lem5325206 m)). Qed.
Lemma lem5325208 (m : real) : (term273 m) = (term270 m).
Proof. exact (TRANS (@lem5325105 m) (@lem5325207 m)). Qed.
Lemma lem5325209 (m : real) : (term270 m) = term43.
Proof. exact (@lem1982719 m). Qed.
Lemma lem5325210 (m : real) : (term273 m) = term43.
Proof. exact (TRANS (@lem5325208 m) (@lem5325209 m)). Qed.
Lemma lem5325211 (l : real) (m : real) : (term243 l m) = term288.
Proof. exact (MK_COMB (@lem5325104 l) (@lem5325210 m)). Qed.
Lemma lem5325212 (l : real) (m : real) : (term242 l m) = term288.
Proof. exact (TRANS (@lem5324996 l m) (@lem5325211 l m)). Qed.
Lemma lem5325213 : term288 = term43.
Proof. exact (@lem1982721 term43). Qed.
Lemma lem5325214 (l : real) (m : real) : (term242 l m) = term43.
Proof. exact (TRANS (@lem5325212 l m) (@lem5325213)). Qed.
Lemma lem5325215 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5325216 (l : real) (m : real) : (term289 l m) = term290.
Proof. exact (MK_COMB (@lem5325215) (@lem5325214 l m)). Qed.
Lemma lem5325217 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5325218 (l : real) (m : real) : (term241 l m) = term291.
Proof. exact (MK_COMB (@lem5325216 l m) (@lem5325217)). Qed.
Lemma lem5325219 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : term291.
Proof. exact (EQ_MP (@lem5325218 l m) (@lem5324995 s t l m h1)). Qed.
Lemma lem5325221 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5325222 : term291 = term292.
Proof. exact (@lem5325221 term43 term43). Qed.
Lemma lem5325224 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5325225 : term43 = term194.
Proof. exact (@lem5325224 (NUMERAL 0)). Qed.
Lemma lem5325227 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5325228 : term43 = term194.
Proof. exact (@lem5325227 (NUMERAL 0)). Qed.
Lemma lem5325229 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5325230 : term195 = term196.
Proof. exact (MK_COMB (@lem5325229) (@lem5325228)). Qed.
Lemma lem5325231 : term292 = term293.
Proof. exact (MK_COMB (@lem5325230) (@lem5325225)). Qed.
Lemma lem5325232 : term294.
Proof. exact (@lem1980255 term43 term78 term43 term78). Qed.
Lemma lem5325234 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325235 : term117 = term118.
Proof. exact (@lem5325234 (NUMERAL 0) term72). Qed.
Lemma lem5325236 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5325237 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5325238 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5325237 h1) (fun h1 : term118 = True => @lem5325236)). Qed.
Lemma lem5325239 : term118 = True.
Proof. exact (EQ_MP (@lem5325238) (@lem5325236)). Qed.
Lemma lem5325240 : term117 = True.
Proof. exact (TRANS (@lem5325235) (@lem5325239)). Qed.
Lemma lem5325241 : True = term117.
Proof. exact (SYM (@lem5325240)). Qed.
Lemma lem5325242 : term117.
Proof. exact (EQ_MP (@lem5325241) (@lem0)). Qed.
Lemma lem5325243 : term295.
Proof. exact (@lem5325232 (@lem5325242)). Qed.
Lemma lem5325245 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325246 : term117 = term118.
Proof. exact (@lem5325245 (NUMERAL 0) term72). Qed.
Lemma lem5325247 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5325248 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5325249 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5325248 h1) (fun h1 : term118 = True => @lem5325247)). Qed.
Lemma lem5325250 : term118 = True.
Proof. exact (EQ_MP (@lem5325249) (@lem5325247)). Qed.
Lemma lem5325251 : term117 = True.
Proof. exact (TRANS (@lem5325246) (@lem5325250)). Qed.
Lemma lem5325252 : True = term117.
Proof. exact (SYM (@lem5325251)). Qed.
Lemma lem5325253 : term117.
Proof. exact (EQ_MP (@lem5325252) (@lem0)). Qed.
Lemma lem5325254 : term293 = term296.
Proof. exact (@lem5325243 (@lem5325253)). Qed.
Lemma lem5325256 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5325257 : term202 = term43.
Proof. exact (@lem5325256 term72). Qed.
Lemma lem5325259 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5325260 : term202 = term43.
Proof. exact (@lem5325259 term72). Qed.
Lemma lem5325261 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5325262 : term203 = term195.
Proof. exact (MK_COMB (@lem5325261) (@lem5325260)). Qed.
Lemma lem5325263 : term296 = term292.
Proof. exact (MK_COMB (@lem5325262) (@lem5325257)). Qed.
Lemma lem5325265 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5325266 : term292 = term297.
Proof. exact (@lem5325265 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5325267 : term297 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5325268 : term292 = False.
Proof. exact (TRANS (@lem5325266) (@lem5325267)). Qed.
Lemma lem5325269 : term296 = False.
Proof. exact (TRANS (@lem5325263) (@lem5325268)). Qed.
Lemma lem5325270 : term293 = False.
Proof. exact (TRANS (@lem5325254) (@lem5325269)). Qed.
Lemma lem5325271 : term292 = False.
Proof. exact (TRANS (@lem5325231) (@lem5325270)). Qed.
Lemma lem5325272 : term291 = False.
Proof. exact (TRANS (@lem5325222) (@lem5325271)). Qed.
Lemma lem5325273 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term192 s t l m) : False.
Proof. exact (EQ_MP (@lem5325272) (@lem5325219 s t l m h1)). Qed.
Lemma lem5325274 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : False.
Proof. exact (or_elim (@lem5324311 s t l m h1) (fun h0 : term192 s t l m => @lem5324792 s t l m h0) (fun h0 : term192 s t l m => @lem5325273 s t l m h0)). Qed.
Lemma lem5325276 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term190 s t l m.
Proof. exact (h1). Qed.
Lemma lem5325277 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : (term190 s t l m) = False.
Proof. exact (prop_ext (fun h2 : term190 s t l m => @lem5325274 s t l m h1) (fun h2 : False => @lem5325276 s t l m h1)). Qed.
Lemma lem5325278 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : False.
Proof. exact (EQ_MP (@lem5325277 s t l m h1) (@lem5325276 s t l m h1)). Qed.
Lemma lem5325279 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term35 s t l m) : term35 s t l m.
Proof. exact (h1). Qed.
Lemma lem5325280 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term35 s t l m) : term190 s t l m.
Proof. exact (EQ_MP (@lem5324301 s t l m) (@lem5325279 s t l m h1)). Qed.
Lemma lem5325281 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term35 s t l m) : (term190 s t l m) = False.
Proof. exact (prop_ext (fun h2 : term190 s t l m => @lem5325278 s t l m h2) (fun h2 : False => @lem5325280 s t l m h1)). Qed.
Lemma lem5325282 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term35 s t l m) : False.
Proof. exact (EQ_MP (@lem5325281 s t l m h1) (@lem5325280 s t l m h1)). Qed.
Lemma lem5325283 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : term298 s t l m.
Proof. exact (fun h0 : term35 s t l m => @lem5325282 s t l m h0). Qed.
Lemma lem5325284 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : term299 s t l m.
Proof. exact (@lem1386578 (term300 s t l m)). Qed.
Lemma lem5325287 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : term300 s t l m.
Proof. exact (@lem5325284 s t l m (@lem5325283 s t l m)). Qed.
Lemma lem5325288 (t : real -> Prop) (l : real) (m : real) (s : real -> Prop) (h1 : term12 s) : term36 t l m.
Proof. exact (@lem5325287 s t l m (@lem5323666 s h1)). Qed.
Lemma lem5325289 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term12 s) (h2 : term12 t) : term32 l m.
Proof. exact (@lem5325288 t l m s h1 (@lem5323698 t h2)). Qed.
Lemma lem5325290 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) : term27 l m.
Proof. exact (@lem5325289 l m s t h1 h2 (@lem5323709 m l h3)). Qed.
Lemma lem5325291 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) : term17 l m.
Proof. exact (ex_intro (term301 l m) (term47 l m) (@lem5325290 s t m l h1 h2 h3)). Qed.
Lemma lem5325292 (c : real) (m : real) (t : real -> Prop) (h1 : term14 m t) : term302 m t c.
Proof. exact (@lem5323699 m t h1 c). Qed.
Lemma lem5325293 (m : real) (t : real -> Prop) (c : real) : (term302 m t c) = (term303 m t c).
Proof. exact (eq_refl (term302 m t c)). Qed.
Lemma lem5325294 (c : real) (m : real) (t : real -> Prop) (h1 : term14 m t) : term303 m t c.
Proof. exact (EQ_MP (@lem5325293 m t c) (@lem5325292 c m t h1)). Qed.
Lemma lem5325295 {A : Type'} (P : A -> Prop) : term304 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem5325296 {A : Type'} (P : A -> Prop) : (term304 A P) = ((term305 A P) = (term306 A P)).
Proof. exact (eq_refl (term304 A P)). Qed.
Lemma lem5325348 (c : real) (m : real) : (real_lt c m) = ((real_lt c m) = True).
Proof. exact (@lem7 (real_lt c m)). Qed.
Lemma lem5325351 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5325352 (m : real) (t : real -> Prop) (c : real) : (term307 m t c) = (term308 m t c).
Proof. exact (@lem5325351 (term303 m t c)). Qed.
Lemma lem5325356 (c : real) (m : real) (h1 : real_lt c m) : (real_lt c m) = True.
Proof. exact (EQ_MP (@lem5325348 c m) (@lem5323712 c m h1)). Qed.
Lemma lem5325357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5325358 (c : real) (m : real) (h1 : real_lt c m) : (term309 c m) = (imp True).
Proof. exact (MK_COMB (@lem5325357) (@lem5325356 c m h1)). Qed.
Lemma lem5325365 (t : real -> Prop) (c : real) : (term310 t c) = (term310 t c).
Proof. exact (eq_refl (term310 t c)). Qed.
Lemma lem5325366 (t : real -> Prop) (c : real) (m : real) (h1 : real_lt c m) : (term303 m t c) = (term311 t c).
Proof. exact (MK_COMB (@lem5325358 c m h1) (@lem5325365 t c)). Qed.
Lemma lem5325368 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5325369 (t : real -> Prop) (c : real) : (term311 t c) = (term310 t c).
Proof. exact (@lem5325368 (term310 t c)). Qed.
Lemma lem5325376 (t : real -> Prop) (c : real) (m : real) (h1 : real_lt c m) : (term303 m t c) = (term310 t c).
Proof. exact (TRANS (@lem5325366 t c m h1) (@lem5325369 t c)). Qed.
Lemma lem5325377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5325378 (t : real -> Prop) (c : real) (m : real) (h1 : real_lt c m) : (term308 m t c) = (term312 t c).
Proof. exact (MK_COMB (@lem5325377) (@lem5325376 t c m h1)). Qed.
Lemma lem5325380 {A : Type'} (P : A -> Prop) : (term305 A P) = (term306 A P).
Proof. exact (EQ_MP (@lem5325296 A P) (@lem5325295 A P)). Qed.
Lemma lem5325381 (P : real -> Prop) : (term313 P) = (term314 P).
Proof. exact (@lem5325380 real P). Qed.
Lemma lem5325382 (t : real -> Prop) (c : real) : (term315 t c) = (term316 t c).
Proof. exact (@lem5325381 (term317 t c)). Qed.
Lemma lem5325383 (t : real -> Prop) (c : real) (x : real) : (term318 t c x) = (term319 t c x).
Proof. exact (eq_refl (term318 t c x)). Qed.
Lemma lem5325384 (t : real -> Prop) (c : real) : (term320 t c) = (term317 t c).
Proof. exact (fun_ext (fun x : real => @lem5325383 t c x)). Qed.
Lemma lem5325385 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325386 (t : real -> Prop) (c : real) : (term321 t c) = (term310 t c).
Proof. exact (MK_COMB (@lem5325385) (@lem5325384 t c)). Qed.
Lemma lem5325387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5325388 (t : real -> Prop) (c : real) : (term315 t c) = (term312 t c).
Proof. exact (MK_COMB (@lem5325387) (@lem5325386 t c)). Qed.
Lemma lem5325389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5325390 (t : real -> Prop) (c : real) : (term322 t c) = (term323 t c).
Proof. exact (MK_COMB (@lem5325389) (@lem5325388 t c)). Qed.
Lemma lem5325391 (t : real -> Prop) (c : real) (x : real) : (term318 t c x) = (term319 t c x).
Proof. exact (eq_refl (term318 t c x)). Qed.
Lemma lem5325392 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5325393 (t : real -> Prop) (c : real) (x : real) : (term324 t c x) = (term325 t c x).
Proof. exact (MK_COMB (@lem5325392) (@lem5325391 t c x)). Qed.
Lemma lem5325394 (t : real -> Prop) (c : real) : (term326 t c) = (term327 t c).
Proof. exact (fun_ext (fun x : real => @lem5325393 t c x)). Qed.
Lemma lem5325395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325396 (t : real -> Prop) (c : real) : (term316 t c) = (term328 t c).
Proof. exact (MK_COMB (@lem5325395) (@lem5325394 t c)). Qed.
Lemma lem5325397 (t : real -> Prop) (c : real) : ((term315 t c) = (term316 t c)) = ((term312 t c) = (term328 t c)).
Proof. exact (MK_COMB (@lem5325390 t c) (@lem5325396 t c)). Qed.
Lemma lem5325398 (t : real -> Prop) (c : real) : (term312 t c) = (term328 t c).
Proof. exact (EQ_MP (@lem5325397 t c) (@lem5325382 t c)). Qed.
Lemma lem5325405 (t : real -> Prop) (c : real) (m : real) (h1 : real_lt c m) : (term308 m t c) = (term328 t c).
Proof. exact (TRANS (@lem5325378 t c m h1) (@lem5325398 t c)). Qed.
Lemma lem5325406 (t : real -> Prop) (c : real) (m : real) (h1 : real_lt c m) : (term307 m t c) = (term328 t c).
Proof. exact (TRANS (@lem5325352 m t c) (@lem5325405 t c m h1)). Qed.
Lemma lem5325407 (t : real -> Prop) (c : real) (m : real) (h1 : real_lt c m) : (term328 t c) = (term307 m t c).
Proof. exact (SYM (@lem5325406 t c m h1)). Qed.
Lemma lem5325410 (t : real -> Prop) (c : real) (x : real) (h1 : term319 t c x) : term319 t c x.
Proof. exact (h1). Qed.
Lemma lem5325411 (c : real) (x : real) (h1 : real_lt c x) : real_lt c x.
Proof. exact (h1). Qed.
Lemma lem5325412 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5325413 (s : real -> Prop) (x : real) (h1 : term329 s x) : term329 s x.
Proof. exact (h1). Qed.
Lemma lem5325414 (s : real -> Prop) (x : real) (y : real) (h1 : term330 s x y) : term330 s x y.
Proof. exact (h1). Qed.
Lemma lem5325415 (x : real) (y : real) (h1 : real_le x y) : real_le x y.
Proof. exact (h1). Qed.
Lemma lem5325416 (y : real) (s : real -> Prop) (h1 : @IN real y s) : @IN real y s.
Proof. exact (h1). Qed.
Lemma lem5325428 (p : Prop) : p = (term15 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5325429 (s : real -> Prop) (x : real) : (term329 s x) = (term331 s x).
Proof. exact (@lem5325428 (term329 s x)). Qed.
Lemma lem5325430 (s : real -> Prop) (x : real) : (term331 s x) = (term329 s x).
Proof. exact (SYM (@lem5325429 s x)). Qed.
Lemma lem5325431 (s : real -> Prop) (x : real) (h1 : term332 s x) : term332 s x.
Proof. exact (h1). Qed.
Lemma lem5325434 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term333 x t s) : term333 x t s.
Proof. exact (h1). Qed.
Lemma lem5325435 (x : real) (t : real -> Prop) (s : real -> Prop) : term334 x t s.
Proof. exact (fun h0 : term333 x t s => @lem5325434 x t s h0). Qed.
Lemma lem5325436 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term334 x t s) : term334 x t s.
Proof. exact (h1). Qed.
Lemma lem5325437 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term333 x t s) : term333 x t s.
Proof. exact (h1). Qed.
Lemma lem5325438 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term333 x t s) (h2 : term334 x t s) : term333 x t s.
Proof. exact (@lem5325436 x t s h2 (@lem5325437 x t s h1)). Qed.
Lemma lem5325439 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term333 x t s) : term335 x t s.
Proof. exact (fun h0 : term334 x t s => @lem5325438 x t s h1 h0). Qed.
Lemma lem5325440 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term334 x t s) : term334 x t s.
Proof. exact (h1). Qed.
Lemma lem5325441 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term333 x t s) (h2 : term334 x t s) : term333 x t s.
Proof. exact (@lem5325439 x t s h1 (@lem5325440 x t s h2)). Qed.
Lemma lem5325442 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term334 x t s) : term334 x t s.
Proof. exact (fun h0 : term333 x t s => @lem5325441 x t s h0 h1). Qed.
Lemma lem5325443 (x : real) (t : real -> Prop) (s : real -> Prop) : term336 x t s.
Proof. exact (fun h0 : term334 x t s => @lem5325442 x t s h0). Qed.
Lemma lem5325446 (x : real) (t : real -> Prop) (s : real -> Prop) : term334 x t s.
Proof. exact (@lem5325443 x t s (@lem5325435 x t s)). Qed.
Lemma lem5325514 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5325515 (t : real -> Prop) (s : real -> Prop) : (term337 t s) = (term338 t s).
Proof. exact (@lem5325514 (term10 t s)). Qed.
Lemma lem5325572 (x : real) (t : real -> Prop) : (term339 x t) = (term339 x t).
Proof. exact (eq_refl (term339 x t)). Qed.
Lemma lem5325573 (x : real) (t : real -> Prop) (s : real -> Prop) : (term340 x t s) = (term341 x t s).
Proof. exact (MK_COMB (@lem5325572 x t) (@lem5325515 t s)). Qed.
Lemma lem5325576 (s : real -> Prop) (x : real) : (term342 s x) = (term342 s x).
Proof. exact (eq_refl (term342 s x)). Qed.
Lemma lem5325577 (x : real) (t : real -> Prop) (s : real -> Prop) : (term333 x t s) = (term343 x t s).
Proof. exact (MK_COMB (@lem5325576 s x) (@lem5325573 x t s)). Qed.
Lemma lem5325580 (t : real -> Prop) (s : real -> Prop) : (term344 t s) = (term345 t s).
Proof. exact (fun_ext (fun x : real => @lem5325577 x t s)). Qed.
Lemma lem5325581 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325582 (t : real -> Prop) (s : real -> Prop) : (term346 t s) = (term347 t s).
Proof. exact (MK_COMB (@lem5325581) (@lem5325580 t s)). Qed.
Lemma lem5325587 (s : real -> Prop) : (term348 s) = (term349 s).
Proof. exact (fun_ext (fun t : real -> Prop => @lem5325582 t s)). Qed.
Lemma lem5325588 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5325589 (s : real -> Prop) : (term350 s) = (term351 s).
Proof. exact (MK_COMB (@lem5325588) (@lem5325587 s)). Qed.
Lemma lem5325594 : term352 = term353.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5325589 s)). Qed.
Lemma lem5325595 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5325604 : term354 = term355.
Proof. exact (MK_COMB (@lem5325595) (@lem5325594)). Qed.
Lemma lem5325609 (s : real -> Prop) (y : real) (x : real) : (term330 s y x) = (term330 s y x).
Proof. exact (eq_refl (term330 s y x)). Qed.
Lemma lem5325610 (s : real -> Prop) (y : real) : (term356 s y) = (term356 s y).
Proof. exact (fun_ext (fun x : real => @lem5325609 s y x)). Qed.
Lemma lem5325611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325612 (s : real -> Prop) (y : real) : (term329 s y) = (term329 s y).
Proof. exact (MK_COMB (@lem5325611) (@lem5325610 s y)). Qed.
Lemma lem5325615 (y : real) (t : real -> Prop) : (term339 y t) = (term339 y t).
Proof. exact (eq_refl (term339 y t)). Qed.
Lemma lem5325616 (t : real -> Prop) (s : real -> Prop) (y : real) : (term357 t s y) = (term357 t s y).
Proof. exact (MK_COMB (@lem5325615 y t) (@lem5325612 s y)). Qed.
Lemma lem5325617 (t : real -> Prop) (s : real -> Prop) : (term358 t s) = (term358 t s).
Proof. exact (fun_ext (fun y : real => @lem5325616 t s y)). Qed.
Lemma lem5325618 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325619 (t : real -> Prop) (s : real -> Prop) : (term10 t s) = (term10 t s).
Proof. exact (MK_COMB (@lem5325618) (@lem5325617 t s)). Qed.
Lemma lem5325620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5325621 (t : real -> Prop) (s : real -> Prop) : (term338 t s) = (term338 t s).
Proof. exact (MK_COMB (@lem5325620) (@lem5325619 t s)). Qed.
Lemma lem5325624 (x : real) (t : real -> Prop) : (term339 x t) = (term339 x t).
Proof. exact (eq_refl (term339 x t)). Qed.
Lemma lem5325625 (x : real) (t : real -> Prop) (s : real -> Prop) : (term341 x t s) = (term341 x t s).
Proof. exact (MK_COMB (@lem5325624 x t) (@lem5325621 t s)). Qed.
Lemma lem5325630 (s : real -> Prop) (x : real) (y : real) : (term330 s x y) = (term330 s x y).
Proof. exact (eq_refl (term330 s x y)). Qed.
Lemma lem5325631 (s : real -> Prop) (x : real) : (term356 s x) = (term356 s x).
Proof. exact (fun_ext (fun y : real => @lem5325630 s x y)). Qed.
Lemma lem5325632 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325633 (s : real -> Prop) (x : real) : (term329 s x) = (term329 s x).
Proof. exact (MK_COMB (@lem5325632) (@lem5325631 s x)). Qed.
Lemma lem5325634 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5325635 (s : real -> Prop) (x : real) : (term332 s x) = (term332 s x).
Proof. exact (MK_COMB (@lem5325634) (@lem5325633 s x)). Qed.
Lemma lem5325636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5325637 (s : real -> Prop) (x : real) : (term342 s x) = (term342 s x).
Proof. exact (MK_COMB (@lem5325636) (@lem5325635 s x)). Qed.
Lemma lem5325638 (x : real) (t : real -> Prop) (s : real -> Prop) : (term343 x t s) = (term343 x t s).
Proof. exact (MK_COMB (@lem5325637 s x) (@lem5325625 x t s)). Qed.
Lemma lem5325639 (t : real -> Prop) (s : real -> Prop) : (term345 t s) = (term345 t s).
Proof. exact (fun_ext (fun x : real => @lem5325638 x t s)). Qed.
Lemma lem5325640 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325641 (t : real -> Prop) (s : real -> Prop) : (term347 t s) = (term347 t s).
Proof. exact (MK_COMB (@lem5325640) (@lem5325639 t s)). Qed.
Lemma lem5325642 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (fun_ext (fun t : real -> Prop => @lem5325641 t s)). Qed.
Lemma lem5325643 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5325644 (s : real -> Prop) : (term351 s) = (term351 s).
Proof. exact (MK_COMB (@lem5325643) (@lem5325642 s)). Qed.
Lemma lem5325645 : term353 = term353.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5325644 s)). Qed.
Lemma lem5325646 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5325647 : term355 = term355.
Proof. exact (MK_COMB (@lem5325646) (@lem5325645)). Qed.
Lemma lem5325696 : term354 = term355.
Proof. exact (TRANS (@lem5325604) (@lem5325647)). Qed.
Lemma lem5325697 : term355 = term354.
Proof. exact (SYM (@lem5325696)). Qed.
Lemma lem5325698 (s : real -> Prop) (x : real) (h1 : term332 s x) : term332 s x.
Proof. exact (h1). Qed.
Lemma lem5325700 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term10 t s.
Proof. exact (h1). Qed.
Lemma lem5325707 (s : real -> Prop) (x : real) (y : real) : (term359 s x y) = (term360 s x y).
Proof. exact (@lem17045 (@IN real y s) (real_le x y)). Qed.
Lemma lem5325708 (P : real -> Prop) : (term361 P) = (term314 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5325709 (s : real -> Prop) (x : real) : (term332 s x) = (term362 s x).
Proof. exact (@lem5325708 (term356 s x)). Qed.
Lemma lem5325710 (s : real -> Prop) (x : real) (y : real) : (term363 s x y) = (term330 s x y).
Proof. exact (eq_refl (term363 s x y)). Qed.
Lemma lem5325711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5325712 (s : real -> Prop) (x : real) (y : real) : (term364 s x y) = (term359 s x y).
Proof. exact (MK_COMB (@lem5325711) (@lem5325710 s x y)). Qed.
Lemma lem5325713 (s : real -> Prop) (x : real) (y : real) : (term364 s x y) = (term360 s x y).
Proof. exact (TRANS (@lem5325712 s x y) (@lem5325707 s x y)). Qed.
Lemma lem5325714 (s : real -> Prop) (x : real) : (term365 s x) = (term366 s x).
Proof. exact (fun_ext (fun y : real => @lem5325713 s x y)). Qed.
Lemma lem5325715 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325716 (s : real -> Prop) (x : real) : (term362 s x) = (term367 s x).
Proof. exact (MK_COMB (@lem5325715) (@lem5325714 s x)). Qed.
Lemma lem5325769 (s : real -> Prop) (x : real) : (term332 s x) = (term367 s x).
Proof. exact (TRANS (@lem5325709 s x) (@lem5325716 s x)). Qed.
Lemma lem5325770 (s : real -> Prop) (x : real) (h1 : term332 s x) : term367 s x.
Proof. exact (EQ_MP (@lem5325769 s x) (@lem5325698 s x h1)). Qed.
Lemma lem5325776 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5325782 (s : real -> Prop) (y : real) (x : real) : (term330 s y x) = (term330 s y x).
Proof. exact (eq_refl (term330 s y x)). Qed.
Lemma lem5325783 (s : real -> Prop) (y : real) : (term356 s y) = (term356 s y).
Proof. exact (fun_ext (fun x : real => @lem5325782 s y x)). Qed.
Lemma lem5325784 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325785 (s : real -> Prop) (y : real) : (term329 s y) = (term329 s y).
Proof. exact (MK_COMB (@lem5325784) (@lem5325783 s y)). Qed.
Lemma lem5325787 (y : real) (t : real -> Prop) : (term368 y t) = (term368 y t).
Proof. exact (eq_refl (term368 y t)). Qed.
Lemma lem5325788 (t : real -> Prop) (s : real -> Prop) (y : real) : (term369 t s y) = (term369 t s y).
Proof. exact (MK_COMB (@lem5325787 y t) (@lem5325785 s y)). Qed.
Lemma lem5325789 (t : real -> Prop) (s : real -> Prop) (y : real) : (term357 t s y) = (term369 t s y).
Proof. exact (@lem17265 (@IN real y t) (term329 s y)). Qed.
Lemma lem5325790 (t : real -> Prop) (s : real -> Prop) (y : real) : (term357 t s y) = (term369 t s y).
Proof. exact (TRANS (@lem5325789 t s y) (@lem5325788 t s y)). Qed.
Lemma lem5325791 (t : real -> Prop) (s : real -> Prop) : (term358 t s) = (term370 t s).
Proof. exact (fun_ext (fun y : real => @lem5325790 t s y)). Qed.
Lemma lem5325792 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325793 (t : real -> Prop) (s : real -> Prop) : (term10 t s) = (term371 t s).
Proof. exact (MK_COMB (@lem5325792) (@lem5325791 t s)). Qed.
Lemma lem5325892 {A : Type'} (P : Prop) (Q : A -> Prop) : (term372 A P Q) = (term373 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5325893 (P : Prop) (Q : real -> Prop) : (term374 P Q) = (term375 P Q).
Proof. exact (@lem5325892 real P Q). Qed.
Lemma lem5325894 (t : real -> Prop) (s : real -> Prop) (y : real) : (term376 t s y) = (term377 t s y).
Proof. exact (@lem5325893 (term378 y t) (term356 s y)). Qed.
Lemma lem5325895 (s : real -> Prop) (y : real) (x : real) : (term363 s y x) = (term330 s y x).
Proof. exact (eq_refl (term363 s y x)). Qed.
Lemma lem5325896 (s : real -> Prop) (y : real) : (term379 s y) = (term356 s y).
Proof. exact (fun_ext (fun x : real => @lem5325895 s y x)). Qed.
Lemma lem5325897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325898 (s : real -> Prop) (y : real) : (term380 s y) = (term329 s y).
Proof. exact (MK_COMB (@lem5325897) (@lem5325896 s y)). Qed.
Lemma lem5325899 (y : real) (t : real -> Prop) : (term368 y t) = (term368 y t).
Proof. exact (eq_refl (term368 y t)). Qed.
Lemma lem5325900 (t : real -> Prop) (s : real -> Prop) (y : real) : (term376 t s y) = (term369 t s y).
Proof. exact (MK_COMB (@lem5325899 y t) (@lem5325898 s y)). Qed.
Lemma lem5325901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5325902 (t : real -> Prop) (s : real -> Prop) (y : real) : (term381 t s y) = (term382 t s y).
Proof. exact (MK_COMB (@lem5325901) (@lem5325900 t s y)). Qed.
Lemma lem5325903 (s : real -> Prop) (y : real) (x : real) : (term363 s y x) = (term330 s y x).
Proof. exact (eq_refl (term363 s y x)). Qed.
Lemma lem5325904 (y : real) (t : real -> Prop) : (term368 y t) = (term368 y t).
Proof. exact (eq_refl (term368 y t)). Qed.
Lemma lem5325905 (t : real -> Prop) (s : real -> Prop) (y : real) (x : real) : (term383 t s y x) = (term384 t s y x).
Proof. exact (MK_COMB (@lem5325904 y t) (@lem5325903 s y x)). Qed.
Lemma lem5325906 (t : real -> Prop) (s : real -> Prop) (y : real) : (term385 t s y) = (term386 t s y).
Proof. exact (fun_ext (fun x : real => @lem5325905 t s y x)). Qed.
Lemma lem5325907 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325908 (t : real -> Prop) (s : real -> Prop) (y : real) : (term377 t s y) = (term387 t s y).
Proof. exact (MK_COMB (@lem5325907) (@lem5325906 t s y)). Qed.
Lemma lem5325909 (t : real -> Prop) (s : real -> Prop) (y : real) : ((term376 t s y) = (term377 t s y)) = ((term369 t s y) = (term387 t s y)).
Proof. exact (MK_COMB (@lem5325902 t s y) (@lem5325908 t s y)). Qed.
Lemma lem5325910 (t : real -> Prop) (s : real -> Prop) (y : real) : (term369 t s y) = (term387 t s y).
Proof. exact (EQ_MP (@lem5325909 t s y) (@lem5325894 t s y)). Qed.
Lemma lem5325911 (t : real -> Prop) (s : real -> Prop) : (term370 t s) = (term388 t s).
Proof. exact (fun_ext (fun y : real => @lem5325910 t s y)). Qed.
Lemma lem5325912 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325913 (t : real -> Prop) (s : real -> Prop) : (term371 t s) = (term389 t s).
Proof. exact (MK_COMB (@lem5325912) (@lem5325911 t s)). Qed.
Lemma lem5325915 {A B : Type'} (P : type1413 A B) : (term390 A B P) = (term391 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5325916 (P : type1626) : (term392 P) = (term393 P).
Proof. exact (@lem5325915 real real P). Qed.
Lemma lem5325917 (t : real -> Prop) (s : real -> Prop) : (term394 t s) = (term395 t s).
Proof. exact (@lem5325916 (term396 t s)). Qed.
Lemma lem5325918 (t : real -> Prop) (s : real -> Prop) (y : real) : (term397 t s y) = (term386 t s y).
Proof. exact (eq_refl (term397 t s y)). Qed.
Lemma lem5325919 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5325920 (t : real -> Prop) (s : real -> Prop) (y : real) (x : real) : (term398 t s y x) = (term399 t s y x).
Proof. exact (MK_COMB (@lem5325918 t s y) (@lem5325919 x)). Qed.
Lemma lem5325921 (t : real -> Prop) (s : real -> Prop) (y : real) (x : real) : (term399 t s y x) = (term384 t s y x).
Proof. exact (eq_refl (term399 t s y x)). Qed.
Lemma lem5325922 (t : real -> Prop) (s : real -> Prop) (y : real) (x : real) : (term398 t s y x) = (term384 t s y x).
Proof. exact (TRANS (@lem5325920 t s y x) (@lem5325921 t s y x)). Qed.
Lemma lem5325923 (t : real -> Prop) (s : real -> Prop) (y : real) : (term400 t s y) = (term386 t s y).
Proof. exact (fun_ext (fun x : real => @lem5325922 t s y x)). Qed.
Lemma lem5325924 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5325925 (t : real -> Prop) (s : real -> Prop) (y : real) : (term401 t s y) = (term387 t s y).
Proof. exact (MK_COMB (@lem5325924) (@lem5325923 t s y)). Qed.
Lemma lem5325926 (t : real -> Prop) (s : real -> Prop) : (term402 t s) = (term388 t s).
Proof. exact (fun_ext (fun y : real => @lem5325925 t s y)). Qed.
Lemma lem5325927 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325928 (t : real -> Prop) (s : real -> Prop) : (term394 t s) = (term389 t s).
Proof. exact (MK_COMB (@lem5325927) (@lem5325926 t s)). Qed.
Lemma lem5325929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5325930 (t : real -> Prop) (s : real -> Prop) : (term403 t s) = (term404 t s).
Proof. exact (MK_COMB (@lem5325929) (@lem5325928 t s)). Qed.
Lemma lem5325931 (t : real -> Prop) (s : real -> Prop) (y : real) : (term397 t s y) = (term386 t s y).
Proof. exact (eq_refl (term397 t s y)). Qed.
Lemma lem5325932 (x : real -> real) (y : real) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5325933 (t : real -> Prop) (s : real -> Prop) (x : real -> real) (y : real) : (term405 t s x y) = (term406 t s x y).
Proof. exact (MK_COMB (@lem5325931 t s y) (@lem5325932 x y)). Qed.
Lemma lem5325934 (t : real -> Prop) (s : real -> Prop) (x : real -> real) (y : real) : (term406 t s x y) = (term407 t s x y).
Proof. exact (eq_refl (term406 t s x y)). Qed.
Lemma lem5325935 (t : real -> Prop) (s : real -> Prop) (x : real -> real) (y : real) : (term405 t s x y) = (term407 t s x y).
Proof. exact (TRANS (@lem5325933 t s x y) (@lem5325934 t s x y)). Qed.
Lemma lem5325936 (t : real -> Prop) (s : real -> Prop) (x : real -> real) : (term408 t s x) = (term409 t s x).
Proof. exact (fun_ext (fun y : real => @lem5325935 t s x y)). Qed.
Lemma lem5325937 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325938 (t : real -> Prop) (s : real -> Prop) (x : real -> real) : (term410 t s x) = (term411 t s x).
Proof. exact (MK_COMB (@lem5325937) (@lem5325936 t s x)). Qed.
Lemma lem5325939 (t : real -> Prop) (s : real -> Prop) : (term412 t s) = (term413 t s).
Proof. exact (fun_ext (fun x : real -> real => @lem5325938 t s x)). Qed.
Lemma lem5325940 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5325941 (t : real -> Prop) (s : real -> Prop) : (term395 t s) = (term414 t s).
Proof. exact (MK_COMB (@lem5325940) (@lem5325939 t s)). Qed.
Lemma lem5325942 (t : real -> Prop) (s : real -> Prop) : ((term394 t s) = (term395 t s)) = ((term389 t s) = (term414 t s)).
Proof. exact (MK_COMB (@lem5325930 t s) (@lem5325941 t s)). Qed.
Lemma lem5325943 (t : real -> Prop) (s : real -> Prop) : (term389 t s) = (term414 t s).
Proof. exact (EQ_MP (@lem5325942 t s) (@lem5325917 t s)). Qed.
Lemma lem5325945 (t : real -> Prop) (s : real -> Prop) : (term371 t s) = (term414 t s).
Proof. exact (TRANS (@lem5325913 t s) (@lem5325943 t s)). Qed.
Lemma lem5325946 (t : real -> Prop) (s : real -> Prop) : (term10 t s) = (term414 t s).
Proof. exact (TRANS (@lem5325793 t s) (@lem5325945 t s)). Qed.
Lemma lem5325947 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term414 t s.
Proof. exact (EQ_MP (@lem5325946 t s) (@lem5325700 t s h1)). Qed.
Lemma lem5325948 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term411 t s x'.
Proof. exact (h1). Qed.
Lemma lem5325965 (s : real -> Prop) (x : real) (y : real) : (term360 s x y) = (term360 s x y).
Proof. exact (eq_refl (term360 s x y)). Qed.
Lemma lem5325966 (s : real -> Prop) (x : real) : (term366 s x) = (term366 s x).
Proof. exact (fun_ext (fun y : real => @lem5325965 s x y)). Qed.
Lemma lem5325967 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5325968 (s : real -> Prop) (x : real) : (term367 s x) = (term367 s x).
Proof. exact (MK_COMB (@lem5325967) (@lem5325966 s x)). Qed.
Lemma lem5325969 (s : real -> Prop) (x : real) (h1 : term332 s x) : term367 s x.
Proof. exact (EQ_MP (@lem5325968 s x) (@lem5325770 s x h1)). Qed.
Lemma lem5325975 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5326002 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (y : real) : (term407 t s x' y) = (term407 t s x' y).
Proof. exact (eq_refl (term407 t s x' y)). Qed.
Lemma lem5326003 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) : (term409 t s x') = (term409 t s x').
Proof. exact (fun_ext (fun y : real => @lem5326002 t s x' y)). Qed.
Lemma lem5326004 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5326005 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) : (term411 t s x') = (term411 t s x').
Proof. exact (MK_COMB (@lem5326004) (@lem5326003 t s x')). Qed.
Lemma lem5326006 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term411 t s x'.
Proof. exact (EQ_MP (@lem5326005 t s x') (@lem5325948 t s x' h1)). Qed.
Lemma lem5326014 (s : real -> Prop) (x : real) (y : real) : (term360 s x y) = (term360 s x y).
Proof. exact (eq_refl (term360 s x y)). Qed.
Lemma lem5326015 (s : real -> Prop) (x : real) : (term366 s x) = (term366 s x).
Proof. exact (fun_ext (fun y : real => @lem5326014 s x y)). Qed.
Lemma lem5326016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5326018 (s : real -> Prop) (x : real) : (term367 s x) = (term367 s x).
Proof. exact (MK_COMB (@lem5326016) (@lem5326015 s x)). Qed.
Lemma lem5326019 (s : real -> Prop) (x : real) (h1 : term332 s x) : term367 s x.
Proof. exact (EQ_MP (@lem5326018 s x) (@lem5325969 s x h1)). Qed.
Lemma lem5326023 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5326041 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) (y : real) : (term407 t s x' y) = (term415 s t x' y).
Proof. exact (@lem19490 (term416 x' y s) (term378 y t) (term417 x' y)). Qed.
Lemma lem5326042 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) : (term409 t s x') = (term418 s t x').
Proof. exact (fun_ext (fun y : real => @lem5326041 s t x' y)). Qed.
Lemma lem5326043 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5326045 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) : (term411 t s x') = (term419 s t x').
Proof. exact (MK_COMB (@lem5326043) (@lem5326042 s t x')). Qed.
Lemma lem5326046 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term419 s t x'.
Proof. exact (EQ_MP (@lem5326045 s t x') (@lem5326006 t s x' h1)). Qed.
Lemma lem5326047 (_69690 : real) (s : real -> Prop) (x : real) (h1 : term332 s x) : term420 s x _69690.
Proof. exact (@lem5326019 s x h1 _69690). Qed.
Lemma lem5326048 (s : real -> Prop) (x : real) (_69690 : real) : (term420 s x _69690) = (term360 s x _69690).
Proof. exact (eq_refl (term420 s x _69690)). Qed.
Lemma lem5326050 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term421 s t x' _69691.
Proof. exact (@lem5326046 t s x' h1 _69691). Qed.
Lemma lem5326051 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) (_69691 : real) : (term421 s t x' _69691) = (term415 s t x' _69691).
Proof. exact (eq_refl (term421 s t x' _69691)). Qed.
Lemma lem5326052 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term415 s t x' _69691.
Proof. exact (EQ_MP (@lem5326051 s t x' _69691) (@lem5326050 _69691 t s x' h1)). Qed.
Lemma lem5326060 (_69690 : real) (s : real -> Prop) (x : real) (h1 : term332 s x) : term360 s x _69690.
Proof. exact (EQ_MP (@lem5326048 s x _69690) (@lem5326047 _69690 s x h1)). Qed.
Lemma lem5326062 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5326068 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term422 t x' _69691 s.
Proof. exact (proj1 (@lem5326052 _69691 t s x' h1)). Qed.
Lemma lem5326074 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term423 t x' _69691.
Proof. exact (proj2 (@lem5326052 _69691 t s x' h1)). Qed.
Lemma lem5326076 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5326077 (x : real) (t : real -> Prop) (h1 : @IN real x t) : term424 x t.
Proof. exact (fun h0 : term378 x t => @lem5326076 x t h1). Qed.
Lemma lem5326079 (p : Prop) : (term425 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5326080 (x : real) (t : real -> Prop) : (term424 x t) = (@IN real x t).
Proof. exact (@lem5326079 (@IN real x t)). Qed.
Lemma lem5326081 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (EQ_MP (@lem5326080 x t) (@lem5326077 x t h1)). Qed.
Lemma lem5326087 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5326088 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : (term422 t x' _69691 s) = (term426 x' s _69691 t).
Proof. exact (@lem5326087 (term416 x' _69691 s) (term378 _69691 t)). Qed.
Lemma lem5326094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5326095 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : (term427 t x' _69691 s) = (term428 x' s _69691 t).
Proof. exact (MK_COMB (@lem5326094) (@lem5326088 x' s _69691 t)). Qed.
Lemma lem5326101 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : (term426 x' s _69691 t) = (term426 x' s _69691 t).
Proof. exact (eq_refl (term426 x' s _69691 t)). Qed.
Lemma lem5326102 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : ((term422 t x' _69691 s) = (term426 x' s _69691 t)) = ((term426 x' s _69691 t) = (term426 x' s _69691 t)).
Proof. exact (MK_COMB (@lem5326095 x' s _69691 t) (@lem5326101 x' s _69691 t)). Qed.
Lemma lem5326104 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5326105 (x : Prop) : (x = x) = True.
Proof. exact (@lem5326104 Prop x). Qed.
Lemma lem5326106 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : ((term426 x' s _69691 t) = (term426 x' s _69691 t)) = True.
Proof. exact (@lem5326105 (term426 x' s _69691 t)). Qed.
Lemma lem5326107 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : ((term422 t x' _69691 s) = (term426 x' s _69691 t)) = True.
Proof. exact (TRANS (@lem5326102 x' s _69691 t) (@lem5326106 x' s _69691 t)). Qed.
Lemma lem5326108 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : True = ((term422 t x' _69691 s) = (term426 x' s _69691 t)).
Proof. exact (SYM (@lem5326107 x' s _69691 t)). Qed.
Lemma lem5326109 (x' : real -> real) (s : real -> Prop) (_69691 : real) (t : real -> Prop) : (term422 t x' _69691 s) = (term426 x' s _69691 t).
Proof. exact (EQ_MP (@lem5326108 x' s _69691 t) (@lem0)). Qed.
Lemma lem5326110 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term426 x' s _69691 t.
Proof. exact (EQ_MP (@lem5326109 x' s _69691 t) (@lem5326068 _69691 t s x' h1)). Qed.
Lemma lem5326112 (b : Prop) (a : Prop) : (a \/ b) = (term429 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5326113 (t : real -> Prop) (x' : real -> real) (_69691 : real) (s : real -> Prop) : (term426 x' s _69691 t) = (term430 t x' _69691 s).
Proof. exact (@lem5326112 (term378 _69691 t) (term416 x' _69691 s)). Qed.
Lemma lem5326115 (a : Prop) : (term431 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5326116 (_69691 : real) (t : real -> Prop) : (term432 _69691 t) = (@IN real _69691 t).
Proof. exact (@lem5326115 (@IN real _69691 t)). Qed.
Lemma lem5326117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5326118 (_69691 : real) (t : real -> Prop) : (term433 _69691 t) = (term339 _69691 t).
Proof. exact (MK_COMB (@lem5326117) (@lem5326116 _69691 t)). Qed.
Lemma lem5326119 (x' : real -> real) (_69691 : real) (s : real -> Prop) : (term416 x' _69691 s) = (term416 x' _69691 s).
Proof. exact (eq_refl (term416 x' _69691 s)). Qed.
Lemma lem5326120 (t : real -> Prop) (x' : real -> real) (_69691 : real) (s : real -> Prop) : (term430 t x' _69691 s) = (term434 t x' _69691 s).
Proof. exact (MK_COMB (@lem5326118 _69691 t) (@lem5326119 x' _69691 s)). Qed.
Lemma lem5326121 (t : real -> Prop) (x' : real -> real) (_69691 : real) (s : real -> Prop) : (term426 x' s _69691 t) = (term434 t x' _69691 s).
Proof. exact (TRANS (@lem5326113 t x' _69691 s) (@lem5326120 t x' _69691 s)). Qed.
Lemma lem5326124 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term434 t x' _69691 s.
Proof. exact (EQ_MP (@lem5326121 t x' _69691 s) (@lem5326110 _69691 t s x' h1)). Qed.
Lemma lem5326125 (x : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term434 t x' x s.
Proof. exact (@lem5326124 x t s x' h1). Qed.
Lemma lem5326128 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term416 x' x s.
Proof. exact (@lem5326125 x t s x' h1 (@lem5326081 x t h2)). Qed.
Lemma lem5326129 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term435 x' x s.
Proof. exact (fun h0 : term436 x' x s => @lem5326128 s x' x t h1 h2). Qed.
Lemma lem5326131 (p : Prop) : (term425 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5326132 (x' : real -> real) (x : real) (s : real -> Prop) : (term435 x' x s) = (term416 x' x s).
Proof. exact (@lem5326131 (term416 x' x s)). Qed.
Lemma lem5326133 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term416 x' x s.
Proof. exact (EQ_MP (@lem5326132 x' x s) (@lem5326129 s x' x t h1 h2)). Qed.
Lemma lem5326135 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5326136 (x : real) (t : real -> Prop) (h1 : @IN real x t) : term424 x t.
Proof. exact (fun h0 : term378 x t => @lem5326135 x t h1). Qed.
Lemma lem5326138 (p : Prop) : (term425 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5326139 (x : real) (t : real -> Prop) : (term424 x t) = (@IN real x t).
Proof. exact (@lem5326138 (@IN real x t)). Qed.
Lemma lem5326140 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (EQ_MP (@lem5326139 x t) (@lem5326136 x t h1)). Qed.
Lemma lem5326146 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5326147 (x' : real -> real) (_69691 : real) (t : real -> Prop) : (term423 t x' _69691) = (term437 x' _69691 t).
Proof. exact (@lem5326146 (term417 x' _69691) (term378 _69691 t)). Qed.
Lemma lem5326153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5326154 (x' : real -> real) (_69691 : real) (t : real -> Prop) : (term438 t x' _69691) = (term439 x' _69691 t).
Proof. exact (MK_COMB (@lem5326153) (@lem5326147 x' _69691 t)). Qed.
Lemma lem5326160 (x' : real -> real) (_69691 : real) (t : real -> Prop) : (term437 x' _69691 t) = (term437 x' _69691 t).
Proof. exact (eq_refl (term437 x' _69691 t)). Qed.
Lemma lem5326161 (x' : real -> real) (_69691 : real) (t : real -> Prop) : ((term423 t x' _69691) = (term437 x' _69691 t)) = ((term437 x' _69691 t) = (term437 x' _69691 t)).
Proof. exact (MK_COMB (@lem5326154 x' _69691 t) (@lem5326160 x' _69691 t)). Qed.
Lemma lem5326163 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5326164 (x : Prop) : (x = x) = True.
Proof. exact (@lem5326163 Prop x). Qed.
Lemma lem5326165 (x' : real -> real) (_69691 : real) (t : real -> Prop) : ((term437 x' _69691 t) = (term437 x' _69691 t)) = True.
Proof. exact (@lem5326164 (term437 x' _69691 t)). Qed.
Lemma lem5326166 (x' : real -> real) (_69691 : real) (t : real -> Prop) : ((term423 t x' _69691) = (term437 x' _69691 t)) = True.
Proof. exact (TRANS (@lem5326161 x' _69691 t) (@lem5326165 x' _69691 t)). Qed.
Lemma lem5326167 (x' : real -> real) (_69691 : real) (t : real -> Prop) : True = ((term423 t x' _69691) = (term437 x' _69691 t)).
Proof. exact (SYM (@lem5326166 x' _69691 t)). Qed.
Lemma lem5326168 (x' : real -> real) (_69691 : real) (t : real -> Prop) : (term423 t x' _69691) = (term437 x' _69691 t).
Proof. exact (EQ_MP (@lem5326167 x' _69691 t) (@lem0)). Qed.
Lemma lem5326169 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term437 x' _69691 t.
Proof. exact (EQ_MP (@lem5326168 x' _69691 t) (@lem5326074 _69691 t s x' h1)). Qed.
Lemma lem5326171 (b : Prop) (a : Prop) : (a \/ b) = (term429 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5326172 (t : real -> Prop) (x' : real -> real) (_69691 : real) : (term437 x' _69691 t) = (term440 t x' _69691).
Proof. exact (@lem5326171 (term378 _69691 t) (term417 x' _69691)). Qed.
Lemma lem5326174 (a : Prop) : (term431 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5326175 (_69691 : real) (t : real -> Prop) : (term432 _69691 t) = (@IN real _69691 t).
Proof. exact (@lem5326174 (@IN real _69691 t)). Qed.
Lemma lem5326176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5326177 (_69691 : real) (t : real -> Prop) : (term433 _69691 t) = (term339 _69691 t).
Proof. exact (MK_COMB (@lem5326176) (@lem5326175 _69691 t)). Qed.
Lemma lem5326178 (x' : real -> real) (_69691 : real) : (term417 x' _69691) = (term417 x' _69691).
Proof. exact (eq_refl (term417 x' _69691)). Qed.
Lemma lem5326179 (t : real -> Prop) (x' : real -> real) (_69691 : real) : (term440 t x' _69691) = (term441 t x' _69691).
Proof. exact (MK_COMB (@lem5326177 _69691 t) (@lem5326178 x' _69691)). Qed.
Lemma lem5326180 (t : real -> Prop) (x' : real -> real) (_69691 : real) : (term437 x' _69691 t) = (term441 t x' _69691).
Proof. exact (TRANS (@lem5326172 t x' _69691) (@lem5326179 t x' _69691)). Qed.
Lemma lem5326183 (_69691 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term441 t x' _69691.
Proof. exact (EQ_MP (@lem5326180 t x' _69691) (@lem5326169 _69691 t s x' h1)). Qed.
Lemma lem5326184 (x : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term411 t s x') : term441 t x' x.
Proof. exact (@lem5326183 x t s x' h1). Qed.
Lemma lem5326187 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term417 x' x.
Proof. exact (@lem5326184 x t s x' h1 (@lem5326140 x t h2)). Qed.
Lemma lem5326188 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term442 x' x.
Proof. exact (fun h0 : term443 x' x => @lem5326187 s x' x t h1 h2). Qed.
Lemma lem5326190 (p : Prop) : (term425 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5326191 (x' : real -> real) (x : real) : (term442 x' x) = (term417 x' x).
Proof. exact (@lem5326190 (term417 x' x)). Qed.
Lemma lem5326192 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term417 x' x.
Proof. exact (EQ_MP (@lem5326191 x' x) (@lem5326188 s x' x t h1 h2)). Qed.
Lemma lem5326194 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5326195 (s : real -> Prop) (x : real) (_69690 : real) : (term360 s x _69690) = (term359 s x _69690).
Proof. exact (@lem5326194 (@IN real _69690 s) (real_le x _69690)). Qed.
Lemma lem5326197 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5326198 (s : real -> Prop) (x : real) (_69690 : real) : (term359 s x _69690) = (term446 s x _69690).
Proof. exact (@lem5326197 (term330 s x _69690)). Qed.
Lemma lem5326199 (s : real -> Prop) (x : real) (_69690 : real) : (term360 s x _69690) = (term446 s x _69690).
Proof. exact (TRANS (@lem5326195 s x _69690) (@lem5326198 s x _69690)). Qed.
Lemma lem5326201 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : @IN real x t) : term447 s x' x.
Proof. exact (conj (@lem5326133 s x' x t h1 h2) (@lem5326192 s x' x t h1 h2)). Qed.
Lemma lem5326203 (_69690 : real) (s : real -> Prop) (x : real) (h1 : term332 s x) : term446 s x _69690.
Proof. exact (EQ_MP (@lem5326199 s x _69690) (@lem5326060 _69690 s x h1)). Qed.
Lemma lem5326204 (x' : real -> real) (s : real -> Prop) (x : real) (h1 : term332 s x) : term448 s x' x.
Proof. exact (@lem5326203 (x' x) s x h1). Qed.
Lemma lem5326207 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (@lem5326204 x' s x h2 (@lem5326201 s x' x t h1 h3)). Qed.
Lemma lem5326208 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : term449.
Proof. exact (fun h0 : ~ False => @lem5326207 x' s x t h1 h2 h3). Qed.
Lemma lem5326210 (p : Prop) : (term425 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5326211 : term449 = False.
Proof. exact (@lem5326210 False). Qed.
Lemma lem5326212 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326211) (@lem5326208 x' s x t h1 h2 h3)). Qed.
Lemma lem5326213 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5326212 x' s x t h1 h2 h3) (fun h4 : False => @lem5326062 x t h3)). Qed.
Lemma lem5326214 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326213 x' s x t h1 h2 h3) (@lem5326062 x t h3)). Qed.
Lemma lem5326215 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5326214 x' s x t h1 h2 h3) (fun h4 : False => @lem5326023 x t h3)). Qed.
Lemma lem5326216 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326215 x' s x t h1 h2 h3) (@lem5326023 x t h3)). Qed.
Lemma lem5326217 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5326216 x' s x t h1 h2 h3) (fun h4 : False => @lem5326023 x t h3)). Qed.
Lemma lem5326218 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326217 x' s x t h1 h2 h3) (@lem5326023 x t h3)). Qed.
Lemma lem5326219 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : (term411 t s x') = False.
Proof. exact (prop_ext (fun h4 : term411 t s x' => @lem5326218 x' s x t h1 h2 h3) (fun h4 : False => @lem5326006 t s x' h1)). Qed.
Lemma lem5326220 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326219 x' s x t h1 h2 h3) (@lem5326006 t s x' h1)). Qed.
Lemma lem5326221 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5326220 x' s x t h1 h2 h3) (fun h4 : False => @lem5325975 x t h3)). Qed.
Lemma lem5326222 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term411 t s x') (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326221 x' s x t h1 h2 h3) (@lem5325975 x t h3)). Qed.
Lemma lem5326223 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (ex_elim (@lem5325947 t s h1) (fun x' : real -> real => fun h0 : term413 t s x' => @lem5326222 x' s x t h0 h2 h3)). Qed.
Lemma lem5326224 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5326223 s x t h1 h2 h3) (fun h4 : False => @lem5325776 x t h3)). Qed.
Lemma lem5326225 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326224 s x t h1 h2 h3) (@lem5325776 x t h3)). Qed.
Lemma lem5326226 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term332 s x) (h2 : @IN real x t) : term337 t s.
Proof. exact (fun h0 : term10 t s => @lem5326225 s x t h0 h1 h2). Qed.
Lemma lem5326227 (t : real -> Prop) (s : real -> Prop) : (term337 t s) = (term338 t s).
Proof. exact (@lem69 (term10 t s)). Qed.
Lemma lem5326228 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term332 s x) (h2 : @IN real x t) : term338 t s.
Proof. exact (EQ_MP (@lem5326227 t s) (@lem5326226 s x t h1 h2)). Qed.
Lemma lem5326229 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term332 s x) : term341 x t s.
Proof. exact (fun h0 : @IN real x t => @lem5326228 s x t h1 h0). Qed.
Lemma lem5326230 (x : real) (t : real -> Prop) (s : real -> Prop) : term343 x t s.
Proof. exact (fun h0 : term332 s x => @lem5326229 t s x h0). Qed.
Lemma lem5326235 (t : real -> Prop) (s : real -> Prop) : term347 t s.
Proof. exact (fun x : real => @lem5326230 x t s). Qed.
Lemma lem5326240 (s : real -> Prop) : term351 s.
Proof. exact (fun t : real -> Prop => @lem5326235 t s). Qed.
Lemma lem5326245 : term355.
Proof. exact (fun s : real -> Prop => @lem5326240 s). Qed.
Lemma lem5326246 : term354.
Proof. exact (EQ_MP (@lem5325697) (@lem5326245)). Qed.
Lemma lem5326247 (s : real -> Prop) : term450 s.
Proof. exact (@lem5326246 s). Qed.
Lemma lem5326248 (s : real -> Prop) : (term450 s) = (term350 s).
Proof. exact (eq_refl (term450 s)). Qed.
Lemma lem5326249 (s : real -> Prop) : term350 s.
Proof. exact (EQ_MP (@lem5326248 s) (@lem5326247 s)). Qed.
Lemma lem5326250 (s : real -> Prop) (t : real -> Prop) : term451 s t.
Proof. exact (@lem5326249 s t). Qed.
Lemma lem5326251 (t : real -> Prop) (s : real -> Prop) : (term451 s t) = (term346 t s).
Proof. exact (eq_refl (term451 s t)). Qed.
Lemma lem5326252 (t : real -> Prop) (s : real -> Prop) : term346 t s.
Proof. exact (EQ_MP (@lem5326251 t s) (@lem5326250 s t)). Qed.
Lemma lem5326253 (t : real -> Prop) (s : real -> Prop) (x : real) : term452 t s x.
Proof. exact (@lem5326252 t s x). Qed.
Lemma lem5326254 (x : real) (t : real -> Prop) (s : real -> Prop) : (term452 t s x) = (term333 x t s).
Proof. exact (eq_refl (term452 t s x)). Qed.
Lemma lem5326255 (x : real) (t : real -> Prop) (s : real -> Prop) : term333 x t s.
Proof. exact (EQ_MP (@lem5326254 x t s) (@lem5326253 t s x)). Qed.
Lemma lem5326257 (x : real) (t : real -> Prop) (s : real -> Prop) : term333 x t s.
Proof. exact (@lem5325446 x t s (@lem5326255 x t s)). Qed.
Lemma lem5326258 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term332 s x) : term340 x t s.
Proof. exact (@lem5326257 x t s (@lem5325431 s x h1)). Qed.
Lemma lem5326259 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term332 s x) (h2 : @IN real x t) : term337 t s.
Proof. exact (@lem5326258 t s x h1 (@lem5325412 x t h2)). Qed.
Lemma lem5326260 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (@lem5326259 s x t h2 h3 (@lem5323636 t s h1)). Qed.
Lemma lem5326261 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : (term10 t s) = False.
Proof. exact (prop_ext (fun h4 : term10 t s => @lem5326260 s x t h1 h2 h3) (fun h4 : False => @lem5323636 t s h1)). Qed.
Lemma lem5326262 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326261 s x t h1 h2 h3) (@lem5323636 t s h1)). Qed.
Lemma lem5326263 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5326262 s x t h1 h2 h3) (fun h4 : False => @lem5325412 x t h3)). Qed.
Lemma lem5326264 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326263 s x t h1 h2 h3) (@lem5325412 x t h3)). Qed.
Lemma lem5326265 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : (term332 s x) = False.
Proof. exact (prop_ext (fun h4 : term332 s x => @lem5326264 s x t h1 h2 h3) (fun h4 : False => @lem5325431 s x h2)). Qed.
Lemma lem5326266 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term332 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5326265 s x t h1 h2 h3) (@lem5325431 s x h2)). Qed.
Lemma lem5326267 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : @IN real x t) : term331 s x.
Proof. exact (fun h0 : term332 s x => @lem5326266 s x t h1 h0 h2). Qed.
Lemma lem5326268 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : @IN real x t) : term329 s x.
Proof. exact (EQ_MP (@lem5325430 s x) (@lem5326267 s x t h1 h2)). Qed.
Lemma lem5326269 (y : real) (s : real -> Prop) (l : real) (h1 : term13 s l) : term453 s l y.
Proof. exact (@lem5323668 s l h1 y). Qed.
Lemma lem5326270 (s : real -> Prop) (y : real) (l : real) : (term453 s l y) = (term454 s y l).
Proof. exact (eq_refl (term453 s l y)). Qed.
Lemma lem5326271 (y : real) (s : real -> Prop) (l : real) (h1 : term13 s l) : term454 s y l.
Proof. exact (EQ_MP (@lem5326270 s y l) (@lem5326269 y s l h1)). Qed.
Lemma lem5326323 (y : real) (s : real -> Prop) : (@IN real y s) = ((@IN real y s) = True).
Proof. exact (@lem7 (@IN real y s)). Qed.
Lemma lem5326328 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5326329 (s : real -> Prop) (y : real) (l : real) : (term455 s y l) = (term456 s y l).
Proof. exact (@lem5326328 (term454 s y l)). Qed.
Lemma lem5326333 (y : real) (s : real -> Prop) (h1 : @IN real y s) : (@IN real y s) = True.
Proof. exact (EQ_MP (@lem5326323 y s) (@lem5325416 y s h1)). Qed.
Lemma lem5326334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5326335 (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term339 y s) = (imp True).
Proof. exact (MK_COMB (@lem5326334) (@lem5326333 y s h1)). Qed.
Lemma lem5326336 (y : real) (l : real) : (real_le y l) = (real_le y l).
Proof. exact (eq_refl (real_le y l)). Qed.
Lemma lem5326337 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term454 s y l) = (term457 y l).
Proof. exact (MK_COMB (@lem5326335 y s h1) (@lem5326336 y l)). Qed.
Lemma lem5326339 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5326340 (y : real) (l : real) : (term457 y l) = (real_le y l).
Proof. exact (@lem5326339 (real_le y l)). Qed.
Lemma lem5326341 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term454 s y l) = (real_le y l).
Proof. exact (TRANS (@lem5326337 l y s h1) (@lem5326340 y l)). Qed.
Lemma lem5326342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5326343 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term456 s y l) = (term3 y l).
Proof. exact (MK_COMB (@lem5326342) (@lem5326341 l y s h1)). Qed.
Lemma lem5326344 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term455 s y l) = (term3 y l).
Proof. exact (TRANS (@lem5326329 s y l) (@lem5326343 l y s h1)). Qed.
Lemma lem5326345 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term3 y l) = (term455 s y l).
Proof. exact (SYM (@lem5326344 l y s h1)). Qed.
Lemma lem5326379 (y : real) (l : real) : (term458 y l) = (real_le y l).
Proof. exact (@lem16933 (real_le y l)). Qed.
Lemma lem5326381 (x : real) (y : real) : (term459 x y) = (term459 x y).
Proof. exact (eq_refl (term459 x y)). Qed.
Lemma lem5326382 (x : real) (y : real) (l : real) : (term460 x y l) = (term461 x y l).
Proof. exact (MK_COMB (@lem5326381 x y) (@lem5326379 y l)). Qed.
Lemma lem5326383 (x : real) (y : real) (l : real) : (term462 x y l) = (term460 x y l).
Proof. exact (@lem17362 (real_le x y) (term3 y l)). Qed.
Lemma lem5326384 (x : real) (y : real) (l : real) : (term462 x y l) = (term461 x y l).
Proof. exact (TRANS (@lem5326383 x y l) (@lem5326382 x y l)). Qed.
Lemma lem5326386 (y : real) (s : real -> Prop) : (term463 y s) = (term463 y s).
Proof. exact (eq_refl (term463 y s)). Qed.
Lemma lem5326387 (s : real -> Prop) (x : real) (y : real) (l : real) : (term464 s x y l) = (term465 s x y l).
Proof. exact (MK_COMB (@lem5326386 y s) (@lem5326384 x y l)). Qed.
Lemma lem5326388 (s : real -> Prop) (x : real) (y : real) (l : real) : (term466 s x y l) = (term464 s x y l).
Proof. exact (@lem17362 (@IN real y s) (term467 x y l)). Qed.
Lemma lem5326389 (s : real -> Prop) (x : real) (y : real) (l : real) : (term466 s x y l) = (term465 s x y l).
Proof. exact (TRANS (@lem5326388 s x y l) (@lem5326387 s x y l)). Qed.
Lemma lem5326391 (c : real) (x : real) : (term23 c x) = (term23 c x).
Proof. exact (eq_refl (term23 c x)). Qed.
Lemma lem5326392 (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term468 c s x y l) = (term469 c s x y l).
Proof. exact (MK_COMB (@lem5326391 c x) (@lem5326389 s x y l)). Qed.
Lemma lem5326393 (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term470 c s x y l) = (term468 c s x y l).
Proof. exact (@lem17362 (real_lt c x) (term471 s x y l)). Qed.
Lemma lem5326394 (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term470 c s x y l) = (term469 c s x y l).
Proof. exact (TRANS (@lem5326393 c s x y l) (@lem5326392 c s x y l)). Qed.
Lemma lem5326396 (x : real) (t : real -> Prop) : (term463 x t) = (term463 x t).
Proof. exact (eq_refl (term463 x t)). Qed.
Lemma lem5326397 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term472 t c s x y l) = (term473 t c s x y l).
Proof. exact (MK_COMB (@lem5326396 x t) (@lem5326394 c s x y l)). Qed.
Lemma lem5326398 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term474 t c s x y l) = (term472 t c s x y l).
Proof. exact (@lem17362 (@IN real x t) (term475 c s x y l)). Qed.
Lemma lem5326399 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term474 t c s x y l) = (term473 t c s x y l).
Proof. exact (TRANS (@lem5326398 t c s x y l) (@lem5326397 t c s x y l)). Qed.
Lemma lem5326401 (c : real) (m : real) : (term23 c m) = (term23 c m).
Proof. exact (eq_refl (term23 c m)). Qed.
Lemma lem5326402 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term476 m t c s x y l) = (term477 m t c s x y l).
Proof. exact (MK_COMB (@lem5326401 c m) (@lem5326399 t c s x y l)). Qed.
Lemma lem5326403 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term478 m t c s x y l) = (term476 m t c s x y l).
Proof. exact (@lem17362 (real_lt c m) (term479 t c s x y l)). Qed.
Lemma lem5326404 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term478 m t c s x y l) = (term477 m t c s x y l).
Proof. exact (TRANS (@lem5326403 m t c s x y l) (@lem5326402 m t c s x y l)). Qed.
Lemma lem5326406 (l : real) (c : real) : (term23 l c) = (term23 l c).
Proof. exact (eq_refl (term23 l c)). Qed.
Lemma lem5326407 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term480 m t c s x y l) = (term481 m t c s x y l).
Proof. exact (MK_COMB (@lem5326406 l c) (@lem5326404 m t c s x y l)). Qed.
Lemma lem5326408 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term482 m t c s x y l) = (term480 m t c s x y l).
Proof. exact (@lem17362 (real_lt l c) (term483 m t c s x y l)). Qed.
Lemma lem5326409 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term482 m t c s x y l) = (term481 m t c s x y l).
Proof. exact (TRANS (@lem5326408 m t c s x y l) (@lem5326407 m t c s x y l)). Qed.
Lemma lem5326411 (l : real) (m : real) : (term23 l m) = (term23 l m).
Proof. exact (eq_refl (term23 l m)). Qed.
Lemma lem5326412 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term484 m t c s x y l) = (term485 m t c s x y l).
Proof. exact (MK_COMB (@lem5326411 l m) (@lem5326409 m t c s x y l)). Qed.
Lemma lem5326413 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term486 m t c s x y l) = (term484 m t c s x y l).
Proof. exact (@lem17362 (real_lt l m) (term487 m t c s x y l)). Qed.
Lemma lem5326414 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term486 m t c s x y l) = (term485 m t c s x y l).
Proof. exact (TRANS (@lem5326413 m t c s x y l) (@lem5326412 m t c s x y l)). Qed.
Lemma lem5326416 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5326417 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term488 m t c s x y l) = (term489 m t c s x y l).
Proof. exact (MK_COMB (@lem5326416 t) (@lem5326414 m t c s x y l)). Qed.
Lemma lem5326418 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term490 m t c s x y l) = (term488 m t c s x y l).
Proof. exact (@lem17362 (term12 t) (term491 m t c s x y l)). Qed.
Lemma lem5326419 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term490 m t c s x y l) = (term489 m t c s x y l).
Proof. exact (TRANS (@lem5326418 m t c s x y l) (@lem5326417 m t c s x y l)). Qed.
Lemma lem5326421 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5326422 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term492 m t c s x y l) = (term493 m t c s x y l).
Proof. exact (MK_COMB (@lem5326421 s) (@lem5326419 m t c s x y l)). Qed.
Lemma lem5326423 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term494 m t c s x y l) = (term492 m t c s x y l).
Proof. exact (@lem17362 (term12 s) (term495 m t c s x y l)). Qed.
Lemma lem5326467 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : (term494 m t c s x y l) = (term493 m t c s x y l).
Proof. exact (TRANS (@lem5326423 m t c s x y l) (@lem5326422 m t c s x y l)). Qed.
Lemma lem5326470 (m : real) (l : real) : (real_lt l m) = (term37 m l).
Proof. exact (@lem1988285 m l). Qed.
Lemma lem5326476 (m : real) (l : real) : (real_sub m l) = (term38 m l).
Proof. exact (@lem1982792 m l). Qed.
Lemma lem5326481 (l : real) (m : real) : (term38 m l) = (term39 l m).
Proof. exact (@lem1982761 (term40 l) m). Qed.
Lemma lem5326483 (l : real) (m : real) : (real_sub m l) = (term39 l m).
Proof. exact (TRANS (@lem5326476 m l) (@lem5326481 l m)). Qed.
Lemma lem5326484 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5326485 (l : real) (m : real) : (term41 m l) = (term42 l m).
Proof. exact (MK_COMB (@lem5326484) (@lem5326483 l m)). Qed.
Lemma lem5326486 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326487 (l : real) (m : real) : (term37 m l) = (term44 l m).
Proof. exact (MK_COMB (@lem5326485 l m) (@lem5326486)). Qed.
Lemma lem5326488 (l : real) (m : real) : (real_lt l m) = (term44 l m).
Proof. exact (TRANS (@lem5326470 m l) (@lem5326487 l m)). Qed.
Lemma lem5326489 (c : real) (l : real) : (real_lt l c) = (term37 c l).
Proof. exact (@lem1988285 c l). Qed.
Lemma lem5326502 (c : real) (l : real) : (real_sub c l) = (term38 c l).
Proof. exact (@lem1982792 c l). Qed.
Lemma lem5326503 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5326504 (c : real) (l : real) : (term41 c l) = (term496 c l).
Proof. exact (MK_COMB (@lem5326503) (@lem5326502 c l)). Qed.
Lemma lem5326505 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326506 (c : real) (l : real) : (term37 c l) = (term497 c l).
Proof. exact (MK_COMB (@lem5326504 c l) (@lem5326505)). Qed.
Lemma lem5326507 (c : real) (l : real) : (real_lt l c) = (term497 c l).
Proof. exact (TRANS (@lem5326489 c l) (@lem5326506 c l)). Qed.
Lemma lem5326508 (m : real) (c : real) : (real_lt c m) = (term37 m c).
Proof. exact (@lem1988285 m c). Qed.
Lemma lem5326514 (m : real) (c : real) : (real_sub m c) = (term38 m c).
Proof. exact (@lem1982792 m c). Qed.
Lemma lem5326519 (c : real) (m : real) : (term38 m c) = (term39 c m).
Proof. exact (@lem1982761 (term40 c) m). Qed.
Lemma lem5326521 (c : real) (m : real) : (real_sub m c) = (term39 c m).
Proof. exact (TRANS (@lem5326514 m c) (@lem5326519 c m)). Qed.
Lemma lem5326522 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5326523 (c : real) (m : real) : (term41 m c) = (term42 c m).
Proof. exact (MK_COMB (@lem5326522) (@lem5326521 c m)). Qed.
Lemma lem5326524 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326525 (c : real) (m : real) : (term37 m c) = (term44 c m).
Proof. exact (MK_COMB (@lem5326523 c m) (@lem5326524)). Qed.
Lemma lem5326526 (c : real) (m : real) : (real_lt c m) = (term44 c m).
Proof. exact (TRANS (@lem5326508 m c) (@lem5326525 c m)). Qed.
Lemma lem5326528 (x : real) (c : real) : (real_lt c x) = (term37 x c).
Proof. exact (@lem1988285 x c). Qed.
Lemma lem5326534 (x : real) (c : real) : (real_sub x c) = (term38 x c).
Proof. exact (@lem1982792 x c). Qed.
Lemma lem5326539 (c : real) (x : real) : (term38 x c) = (term39 c x).
Proof. exact (@lem1982761 (term40 c) x). Qed.
Lemma lem5326541 (c : real) (x : real) : (real_sub x c) = (term39 c x).
Proof. exact (TRANS (@lem5326534 x c) (@lem5326539 c x)). Qed.
Lemma lem5326542 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5326543 (c : real) (x : real) : (term41 x c) = (term42 c x).
Proof. exact (MK_COMB (@lem5326542) (@lem5326541 c x)). Qed.
Lemma lem5326544 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326545 (c : real) (x : real) : (term37 x c) = (term44 c x).
Proof. exact (MK_COMB (@lem5326543 c x) (@lem5326544)). Qed.
Lemma lem5326546 (c : real) (x : real) : (real_lt c x) = (term44 c x).
Proof. exact (TRANS (@lem5326528 x c) (@lem5326545 c x)). Qed.
Lemma lem5326548 (y : real) (x : real) : (real_le x y) = (term498 y x).
Proof. exact (@lem1988287 y x). Qed.
Lemma lem5326554 (y : real) (x : real) : (real_sub y x) = (term38 y x).
Proof. exact (@lem1982792 y x). Qed.
Lemma lem5326559 (x : real) (y : real) : (term38 y x) = (term39 x y).
Proof. exact (@lem1982761 (term40 x) y). Qed.
Lemma lem5326561 (x : real) (y : real) : (real_sub y x) = (term39 x y).
Proof. exact (TRANS (@lem5326554 y x) (@lem5326559 x y)). Qed.
Lemma lem5326562 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5326563 (x : real) (y : real) : (term499 y x) = (term500 x y).
Proof. exact (MK_COMB (@lem5326562) (@lem5326561 x y)). Qed.
Lemma lem5326564 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326565 (x : real) (y : real) : (term498 y x) = (term501 x y).
Proof. exact (MK_COMB (@lem5326563 x y) (@lem5326564)). Qed.
Lemma lem5326566 (x : real) (y : real) : (real_le x y) = (term501 x y).
Proof. exact (TRANS (@lem5326548 y x) (@lem5326565 x y)). Qed.
Lemma lem5326567 (l : real) (y : real) : (real_le y l) = (term498 l y).
Proof. exact (@lem1988287 l y). Qed.
Lemma lem5326580 (l : real) (y : real) : (real_sub l y) = (term38 l y).
Proof. exact (@lem1982792 l y). Qed.
Lemma lem5326581 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5326582 (l : real) (y : real) : (term499 l y) = (term502 l y).
Proof. exact (MK_COMB (@lem5326581) (@lem5326580 l y)). Qed.
Lemma lem5326583 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326584 (l : real) (y : real) : (term498 l y) = (term503 l y).
Proof. exact (MK_COMB (@lem5326582 l y) (@lem5326583)). Qed.
Lemma lem5326585 (l : real) (y : real) : (real_le y l) = (term503 l y).
Proof. exact (TRANS (@lem5326567 l y) (@lem5326584 l y)). Qed.
Lemma lem5326586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5326587 (x : real) (y : real) : (term459 x y) = (term504 x y).
Proof. exact (MK_COMB (@lem5326586) (@lem5326566 x y)). Qed.
Lemma lem5326588 (x : real) (l : real) (y : real) : (term461 x y l) = (term505 x l y).
Proof. exact (MK_COMB (@lem5326587 x y) (@lem5326585 l y)). Qed.
Lemma lem5326590 (y : real) (s : real -> Prop) : (term463 y s) = (term463 y s).
Proof. exact (eq_refl (term463 y s)). Qed.
Lemma lem5326591 (s : real -> Prop) (x : real) (l : real) (y : real) : (term465 s x y l) = (term506 s x l y).
Proof. exact (MK_COMB (@lem5326590 y s) (@lem5326588 x l y)). Qed.
Lemma lem5326592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5326593 (c : real) (x : real) : (term23 c x) = (term181 c x).
Proof. exact (MK_COMB (@lem5326592) (@lem5326546 c x)). Qed.
Lemma lem5326594 (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term469 c s x y l) = (term507 c s x l y).
Proof. exact (MK_COMB (@lem5326593 c x) (@lem5326591 s x l y)). Qed.
Lemma lem5326596 (x : real) (t : real -> Prop) : (term463 x t) = (term463 x t).
Proof. exact (eq_refl (term463 x t)). Qed.
Lemma lem5326597 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term473 t c s x y l) = (term508 t c s x l y).
Proof. exact (MK_COMB (@lem5326596 x t) (@lem5326594 c s x l y)). Qed.
Lemma lem5326598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5326599 (c : real) (m : real) : (term23 c m) = (term181 c m).
Proof. exact (MK_COMB (@lem5326598) (@lem5326526 c m)). Qed.
Lemma lem5326600 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term477 m t c s x y l) = (term509 m t c s x l y).
Proof. exact (MK_COMB (@lem5326599 c m) (@lem5326597 t c s x l y)). Qed.
Lemma lem5326601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5326602 (c : real) (l : real) : (term23 l c) = (term510 c l).
Proof. exact (MK_COMB (@lem5326601) (@lem5326507 c l)). Qed.
Lemma lem5326603 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term481 m t c s x y l) = (term511 m t c s x l y).
Proof. exact (MK_COMB (@lem5326602 c l) (@lem5326600 m t c s x l y)). Qed.
Lemma lem5326604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5326605 (l : real) (m : real) : (term23 l m) = (term181 l m).
Proof. exact (MK_COMB (@lem5326604) (@lem5326488 l m)). Qed.
Lemma lem5326606 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term485 m t c s x y l) = (term512 m t c s x l y).
Proof. exact (MK_COMB (@lem5326605 l m) (@lem5326603 m t c s x l y)). Qed.
Lemma lem5326608 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5326609 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term489 m t c s x y l) = (term513 m t c s x l y).
Proof. exact (MK_COMB (@lem5326608 t) (@lem5326606 m t c s x l y)). Qed.
Lemma lem5326611 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5326612 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term493 m t c s x y l) = (term514 m t c s x l y).
Proof. exact (MK_COMB (@lem5326611 s) (@lem5326609 m t c s x l y)). Qed.
Lemma lem5326675 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term494 m t c s x y l) = (term514 m t c s x l y).
Proof. exact (TRANS (@lem5326467 m t c s x y l) (@lem5326612 m t c s x l y)). Qed.
Lemma lem5326679 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term514 m t c s x l y.
Proof. exact (h1). Qed.
Lemma lem5326680 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term513 m t c s x l y.
Proof. exact (proj2 (@lem5326679 m t c s x l y h1)). Qed.
Lemma lem5326682 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term512 m t c s x l y.
Proof. exact (proj2 (@lem5326680 m t c s x l y h1)). Qed.
Lemma lem5326684 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term511 m t c s x l y.
Proof. exact (proj2 (@lem5326682 m t c s x l y h1)). Qed.
Lemma lem5326686 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term509 m t c s x l y.
Proof. exact (proj2 (@lem5326684 m t c s x l y h1)). Qed.
Lemma lem5326687 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term497 c l.
Proof. exact (proj1 (@lem5326684 m t c s x l y h1)). Qed.
Lemma lem5326688 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term508 t c s x l y.
Proof. exact (proj2 (@lem5326686 m t c s x l y h1)). Qed.
Lemma lem5326690 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term507 c s x l y.
Proof. exact (proj2 (@lem5326688 m t c s x l y h1)). Qed.
Lemma lem5326692 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term506 s x l y.
Proof. exact (proj2 (@lem5326690 m t c s x l y h1)). Qed.
Lemma lem5326693 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term44 c x.
Proof. exact (proj1 (@lem5326690 m t c s x l y h1)). Qed.
Lemma lem5326694 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term505 x l y.
Proof. exact (proj2 (@lem5326692 m t c s x l y h1)). Qed.
Lemma lem5326696 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term503 l y.
Proof. exact (proj2 (@lem5326694 m t c s x l y h1)). Qed.
Lemma lem5326697 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term501 x y.
Proof. exact (proj1 (@lem5326694 m t c s x l y h1)). Qed.
Lemma lem5326699 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5326700 : term193 = term117.
Proof. exact (@lem5326699 term43 term78). Qed.
Lemma lem5326702 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326703 : term78 = term107.
Proof. exact (@lem5326702 term72). Qed.
Lemma lem5326705 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326706 : term43 = term194.
Proof. exact (@lem5326705 (NUMERAL 0)). Qed.
Lemma lem5326707 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5326708 : term195 = term196.
Proof. exact (MK_COMB (@lem5326707) (@lem5326706)). Qed.
Lemma lem5326709 : term117 = term197.
Proof. exact (MK_COMB (@lem5326708) (@lem5326703)). Qed.
Lemma lem5326710 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5326712 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326713 : term117 = term118.
Proof. exact (@lem5326712 (NUMERAL 0) term72). Qed.
Lemma lem5326714 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326715 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326716 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326715 h1) (fun h1 : term118 = True => @lem5326714)). Qed.
Lemma lem5326717 : term118 = True.
Proof. exact (EQ_MP (@lem5326716) (@lem5326714)). Qed.
Lemma lem5326718 : term117 = True.
Proof. exact (TRANS (@lem5326713) (@lem5326717)). Qed.
Lemma lem5326719 : True = term117.
Proof. exact (SYM (@lem5326718)). Qed.
Lemma lem5326720 : term117.
Proof. exact (EQ_MP (@lem5326719) (@lem0)). Qed.
Lemma lem5326721 : term199.
Proof. exact (@lem5326710 (@lem5326720)). Qed.
Lemma lem5326723 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326724 : term117 = term118.
Proof. exact (@lem5326723 (NUMERAL 0) term72). Qed.
Lemma lem5326725 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326726 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326727 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326726 h1) (fun h1 : term118 = True => @lem5326725)). Qed.
Lemma lem5326728 : term118 = True.
Proof. exact (EQ_MP (@lem5326727) (@lem5326725)). Qed.
Lemma lem5326729 : term117 = True.
Proof. exact (TRANS (@lem5326724) (@lem5326728)). Qed.
Lemma lem5326730 : True = term117.
Proof. exact (SYM (@lem5326729)). Qed.
Lemma lem5326731 : term117.
Proof. exact (EQ_MP (@lem5326730) (@lem0)). Qed.
Lemma lem5326732 : term197 = term200.
Proof. exact (@lem5326721 (@lem5326731)). Qed.
Lemma lem5326734 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5326735 : term166 = term92.
Proof. exact (@lem5326734 term72 term72). Qed.
Lemma lem5326736 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5326737 : term91 = term72.
Proof. exact (EQ_MP (@lem5326736) (@lem940073)). Qed.
Lemma lem5326738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5326739 : term92 = term78.
Proof. exact (MK_COMB (@lem5326738) (@lem5326737)). Qed.
Lemma lem5326740 : term166 = term78.
Proof. exact (TRANS (@lem5326735) (@lem5326739)). Qed.
Lemma lem5326742 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5326743 : term202 = term43.
Proof. exact (@lem5326742 term72). Qed.
Lemma lem5326744 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5326745 : term203 = term195.
Proof. exact (MK_COMB (@lem5326744) (@lem5326743)). Qed.
Lemma lem5326746 : term200 = term117.
Proof. exact (MK_COMB (@lem5326745) (@lem5326740)). Qed.
Lemma lem5326748 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326749 : term117 = term118.
Proof. exact (@lem5326748 (NUMERAL 0) term72). Qed.
Lemma lem5326750 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326751 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326752 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326751 h1) (fun h1 : term118 = True => @lem5326750)). Qed.
Lemma lem5326753 : term118 = True.
Proof. exact (EQ_MP (@lem5326752) (@lem5326750)). Qed.
Lemma lem5326754 : term117 = True.
Proof. exact (TRANS (@lem5326749) (@lem5326753)). Qed.
Lemma lem5326755 : term200 = True.
Proof. exact (TRANS (@lem5326746) (@lem5326754)). Qed.
Lemma lem5326756 : term197 = True.
Proof. exact (TRANS (@lem5326732) (@lem5326755)). Qed.
Lemma lem5326757 : term117 = True.
Proof. exact (TRANS (@lem5326709) (@lem5326756)). Qed.
Lemma lem5326758 : term193 = True.
Proof. exact (TRANS (@lem5326700) (@lem5326757)). Qed.
Lemma lem5326759 : True = term193.
Proof. exact (SYM (@lem5326758)). Qed.
Lemma lem5326760 : term193.
Proof. exact (EQ_MP (@lem5326759) (@lem0)). Qed.
Lemma lem5326761 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term515 x y.
Proof. exact (conj (@lem5326760) (@lem5326697 m t c s x l y h1)). Qed.
Lemma lem5326763 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5326764 (x : real) (y : real) : term516 x y.
Proof. exact (@lem5326763 term78 (term39 x y)). Qed.
Lemma lem5326765 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term517 x y.
Proof. exact (@lem5326764 x y (@lem5326761 m t c s x l y h1)). Qed.
Lemma lem5326766 (x : real) (y : real) : (term518 x y) = (term39 x y).
Proof. exact (@lem1982733 (term39 x y)). Qed.
Lemma lem5326767 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5326768 (x : real) (y : real) : (term519 x y) = (term500 x y).
Proof. exact (MK_COMB (@lem5326767) (@lem5326766 x y)). Qed.
Lemma lem5326769 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326770 (x : real) (y : real) : (term517 x y) = (term501 x y).
Proof. exact (MK_COMB (@lem5326768 x y) (@lem5326769)). Qed.
Lemma lem5326771 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term501 x y.
Proof. exact (EQ_MP (@lem5326770 x y) (@lem5326765 m t c s x l y h1)). Qed.
Lemma lem5326773 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5326774 : term193 = term117.
Proof. exact (@lem5326773 term43 term78). Qed.
Lemma lem5326776 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326777 : term78 = term107.
Proof. exact (@lem5326776 term72). Qed.
Lemma lem5326779 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326780 : term43 = term194.
Proof. exact (@lem5326779 (NUMERAL 0)). Qed.
Lemma lem5326781 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5326782 : term195 = term196.
Proof. exact (MK_COMB (@lem5326781) (@lem5326780)). Qed.
Lemma lem5326783 : term117 = term197.
Proof. exact (MK_COMB (@lem5326782) (@lem5326777)). Qed.
Lemma lem5326784 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5326786 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326787 : term117 = term118.
Proof. exact (@lem5326786 (NUMERAL 0) term72). Qed.
Lemma lem5326788 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326789 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326790 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326789 h1) (fun h1 : term118 = True => @lem5326788)). Qed.
Lemma lem5326791 : term118 = True.
Proof. exact (EQ_MP (@lem5326790) (@lem5326788)). Qed.
Lemma lem5326792 : term117 = True.
Proof. exact (TRANS (@lem5326787) (@lem5326791)). Qed.
Lemma lem5326793 : True = term117.
Proof. exact (SYM (@lem5326792)). Qed.
Lemma lem5326794 : term117.
Proof. exact (EQ_MP (@lem5326793) (@lem0)). Qed.
Lemma lem5326795 : term199.
Proof. exact (@lem5326784 (@lem5326794)). Qed.
Lemma lem5326797 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326798 : term117 = term118.
Proof. exact (@lem5326797 (NUMERAL 0) term72). Qed.
Lemma lem5326799 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326800 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326801 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326800 h1) (fun h1 : term118 = True => @lem5326799)). Qed.
Lemma lem5326802 : term118 = True.
Proof. exact (EQ_MP (@lem5326801) (@lem5326799)). Qed.
Lemma lem5326803 : term117 = True.
Proof. exact (TRANS (@lem5326798) (@lem5326802)). Qed.
Lemma lem5326804 : True = term117.
Proof. exact (SYM (@lem5326803)). Qed.
Lemma lem5326805 : term117.
Proof. exact (EQ_MP (@lem5326804) (@lem0)). Qed.
Lemma lem5326806 : term197 = term200.
Proof. exact (@lem5326795 (@lem5326805)). Qed.
Lemma lem5326808 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5326809 : term166 = term92.
Proof. exact (@lem5326808 term72 term72). Qed.
Lemma lem5326810 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5326811 : term91 = term72.
Proof. exact (EQ_MP (@lem5326810) (@lem940073)). Qed.
Lemma lem5326812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5326813 : term92 = term78.
Proof. exact (MK_COMB (@lem5326812) (@lem5326811)). Qed.
Lemma lem5326814 : term166 = term78.
Proof. exact (TRANS (@lem5326809) (@lem5326813)). Qed.
Lemma lem5326816 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5326817 : term202 = term43.
Proof. exact (@lem5326816 term72). Qed.
Lemma lem5326818 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5326819 : term203 = term195.
Proof. exact (MK_COMB (@lem5326818) (@lem5326817)). Qed.
Lemma lem5326820 : term200 = term117.
Proof. exact (MK_COMB (@lem5326819) (@lem5326814)). Qed.
Lemma lem5326822 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326823 : term117 = term118.
Proof. exact (@lem5326822 (NUMERAL 0) term72). Qed.
Lemma lem5326824 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326825 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326826 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326825 h1) (fun h1 : term118 = True => @lem5326824)). Qed.
Lemma lem5326827 : term118 = True.
Proof. exact (EQ_MP (@lem5326826) (@lem5326824)). Qed.
Lemma lem5326828 : term117 = True.
Proof. exact (TRANS (@lem5326823) (@lem5326827)). Qed.
Lemma lem5326829 : term200 = True.
Proof. exact (TRANS (@lem5326820) (@lem5326828)). Qed.
Lemma lem5326830 : term197 = True.
Proof. exact (TRANS (@lem5326806) (@lem5326829)). Qed.
Lemma lem5326831 : term117 = True.
Proof. exact (TRANS (@lem5326783) (@lem5326830)). Qed.
Lemma lem5326832 : term193 = True.
Proof. exact (TRANS (@lem5326774) (@lem5326831)). Qed.
Lemma lem5326833 : True = term193.
Proof. exact (SYM (@lem5326832)). Qed.
Lemma lem5326834 : term193.
Proof. exact (EQ_MP (@lem5326833) (@lem0)). Qed.
Lemma lem5326835 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term520 l y.
Proof. exact (conj (@lem5326834) (@lem5326696 m t c s x l y h1)). Qed.
Lemma lem5326837 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5326838 (l : real) (y : real) : term521 l y.
Proof. exact (@lem5326837 term78 (term38 l y)). Qed.
Lemma lem5326839 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term522 l y.
Proof. exact (@lem5326838 l y (@lem5326835 m t c s x l y h1)). Qed.
Lemma lem5326840 (l : real) (y : real) : (term523 l y) = (term38 l y).
Proof. exact (@lem1982733 (term38 l y)). Qed.
Lemma lem5326841 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5326842 (l : real) (y : real) : (term524 l y) = (term502 l y).
Proof. exact (MK_COMB (@lem5326841) (@lem5326840 l y)). Qed.
Lemma lem5326843 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326844 (l : real) (y : real) : (term522 l y) = (term503 l y).
Proof. exact (MK_COMB (@lem5326842 l y) (@lem5326843)). Qed.
Lemma lem5326845 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term503 l y.
Proof. exact (EQ_MP (@lem5326844 l y) (@lem5326839 m t c s x l y h1)). Qed.
Lemma lem5326847 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5326848 : term193 = term117.
Proof. exact (@lem5326847 term43 term78). Qed.
Lemma lem5326850 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326851 : term78 = term107.
Proof. exact (@lem5326850 term72). Qed.
Lemma lem5326853 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326854 : term43 = term194.
Proof. exact (@lem5326853 (NUMERAL 0)). Qed.
Lemma lem5326855 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5326856 : term195 = term196.
Proof. exact (MK_COMB (@lem5326855) (@lem5326854)). Qed.
Lemma lem5326857 : term117 = term197.
Proof. exact (MK_COMB (@lem5326856) (@lem5326851)). Qed.
Lemma lem5326858 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5326860 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326861 : term117 = term118.
Proof. exact (@lem5326860 (NUMERAL 0) term72). Qed.
Lemma lem5326862 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326863 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326864 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326863 h1) (fun h1 : term118 = True => @lem5326862)). Qed.
Lemma lem5326865 : term118 = True.
Proof. exact (EQ_MP (@lem5326864) (@lem5326862)). Qed.
Lemma lem5326866 : term117 = True.
Proof. exact (TRANS (@lem5326861) (@lem5326865)). Qed.
Lemma lem5326867 : True = term117.
Proof. exact (SYM (@lem5326866)). Qed.
Lemma lem5326868 : term117.
Proof. exact (EQ_MP (@lem5326867) (@lem0)). Qed.
Lemma lem5326869 : term199.
Proof. exact (@lem5326858 (@lem5326868)). Qed.
Lemma lem5326871 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326872 : term117 = term118.
Proof. exact (@lem5326871 (NUMERAL 0) term72). Qed.
Lemma lem5326873 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326874 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326875 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326874 h1) (fun h1 : term118 = True => @lem5326873)). Qed.
Lemma lem5326876 : term118 = True.
Proof. exact (EQ_MP (@lem5326875) (@lem5326873)). Qed.
Lemma lem5326877 : term117 = True.
Proof. exact (TRANS (@lem5326872) (@lem5326876)). Qed.
Lemma lem5326878 : True = term117.
Proof. exact (SYM (@lem5326877)). Qed.
Lemma lem5326879 : term117.
Proof. exact (EQ_MP (@lem5326878) (@lem0)). Qed.
Lemma lem5326880 : term197 = term200.
Proof. exact (@lem5326869 (@lem5326879)). Qed.
Lemma lem5326882 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5326883 : term166 = term92.
Proof. exact (@lem5326882 term72 term72). Qed.
Lemma lem5326884 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5326885 : term91 = term72.
Proof. exact (EQ_MP (@lem5326884) (@lem940073)). Qed.
Lemma lem5326886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5326887 : term92 = term78.
Proof. exact (MK_COMB (@lem5326886) (@lem5326885)). Qed.
Lemma lem5326888 : term166 = term78.
Proof. exact (TRANS (@lem5326883) (@lem5326887)). Qed.
Lemma lem5326890 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5326891 : term202 = term43.
Proof. exact (@lem5326890 term72). Qed.
Lemma lem5326892 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5326893 : term203 = term195.
Proof. exact (MK_COMB (@lem5326892) (@lem5326891)). Qed.
Lemma lem5326894 : term200 = term117.
Proof. exact (MK_COMB (@lem5326893) (@lem5326888)). Qed.
Lemma lem5326896 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326897 : term117 = term118.
Proof. exact (@lem5326896 (NUMERAL 0) term72). Qed.
Lemma lem5326898 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326899 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326900 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326899 h1) (fun h1 : term118 = True => @lem5326898)). Qed.
Lemma lem5326901 : term118 = True.
Proof. exact (EQ_MP (@lem5326900) (@lem5326898)). Qed.
Lemma lem5326902 : term117 = True.
Proof. exact (TRANS (@lem5326897) (@lem5326901)). Qed.
Lemma lem5326903 : term200 = True.
Proof. exact (TRANS (@lem5326894) (@lem5326902)). Qed.
Lemma lem5326904 : term197 = True.
Proof. exact (TRANS (@lem5326880) (@lem5326903)). Qed.
Lemma lem5326905 : term117 = True.
Proof. exact (TRANS (@lem5326857) (@lem5326904)). Qed.
Lemma lem5326906 : term193 = True.
Proof. exact (TRANS (@lem5326848) (@lem5326905)). Qed.
Lemma lem5326907 : True = term193.
Proof. exact (SYM (@lem5326906)). Qed.
Lemma lem5326908 : term193.
Proof. exact (EQ_MP (@lem5326907) (@lem0)). Qed.
Lemma lem5326909 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term525 c l.
Proof. exact (conj (@lem5326908) (@lem5326687 m t c s x l y h1)). Qed.
Lemma lem5326911 (x : real) (y : real) : term219 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5326912 (c : real) (l : real) : term526 c l.
Proof. exact (@lem5326911 term78 (term38 c l)). Qed.
Lemma lem5326913 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term527 c l.
Proof. exact (@lem5326912 c l (@lem5326909 m t c s x l y h1)). Qed.
Lemma lem5326914 (c : real) (l : real) : (term523 c l) = (term38 c l).
Proof. exact (@lem1982733 (term38 c l)). Qed.
Lemma lem5326915 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5326916 (c : real) (l : real) : (term528 c l) = (term496 c l).
Proof. exact (MK_COMB (@lem5326915) (@lem5326914 c l)). Qed.
Lemma lem5326917 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5326918 (c : real) (l : real) : (term527 c l) = (term497 c l).
Proof. exact (MK_COMB (@lem5326916 c l) (@lem5326917)). Qed.
Lemma lem5326919 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term497 c l.
Proof. exact (EQ_MP (@lem5326918 c l) (@lem5326913 m t c s x l y h1)). Qed.
Lemma lem5326920 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term529 c l y.
Proof. exact (conj (@lem5326919 m t c s x l y h1) (@lem5326845 m t c s x l y h1)). Qed.
Lemma lem5326922 (x : real) (y : real) : term239 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5326923 (c : real) (l : real) (y : real) : term530 c l y.
Proof. exact (@lem5326922 (term38 c l) (term38 l y)). Qed.
Lemma lem5326924 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term531 c l y.
Proof. exact (@lem5326923 c l y (@lem5326920 m t c s x l y h1)). Qed.
Lemma lem5326925 (c : real) (l : real) (y : real) : (term532 c l y) = (term533 c l y).
Proof. exact (@lem1982755 c (term40 l) (term38 l y)). Qed.
Lemma lem5326926 (l : real) (y : real) : (term534 l y) = (term535 l y).
Proof. exact (@lem1982763 (term40 l) l (term40 y)). Qed.
Lemma lem5326927 (l : real) : (term536 l) = (term537 l).
Proof. exact (@lem1982713 term66 l). Qed.
Lemma lem5326929 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5326930 : term78 = term107.
Proof. exact (@lem5326929 term72). Qed.
Lemma lem5326932 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5326933 : term66 = term71.
Proof. exact (@lem5326932 term72). Qed.
Lemma lem5326934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5326935 : term123 = term538.
Proof. exact (MK_COMB (@lem5326934) (@lem5326933)). Qed.
Lemma lem5326936 : term539 = term540.
Proof. exact (MK_COMB (@lem5326935) (@lem5326930)). Qed.
Lemma lem5326937 : term541.
Proof. exact (@lem1981473 term66 term78 term78 term78 term43 term78). Qed.
Lemma lem5326939 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326940 : term117 = term118.
Proof. exact (@lem5326939 (NUMERAL 0) term72). Qed.
Lemma lem5326941 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326942 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326943 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326942 h1) (fun h1 : term118 = True => @lem5326941)). Qed.
Lemma lem5326944 : term118 = True.
Proof. exact (EQ_MP (@lem5326943) (@lem5326941)). Qed.
Lemma lem5326945 : term117 = True.
Proof. exact (TRANS (@lem5326940) (@lem5326944)). Qed.
Lemma lem5326946 : True = term117.
Proof. exact (SYM (@lem5326945)). Qed.
Lemma lem5326947 : term117.
Proof. exact (EQ_MP (@lem5326946) (@lem0)). Qed.
Lemma lem5326948 : term542.
Proof. exact (@lem5326937 (@lem5326947)). Qed.
Lemma lem5326950 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326951 : term117 = term118.
Proof. exact (@lem5326950 (NUMERAL 0) term72). Qed.
Lemma lem5326952 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326953 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326954 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326953 h1) (fun h1 : term118 = True => @lem5326952)). Qed.
Lemma lem5326955 : term118 = True.
Proof. exact (EQ_MP (@lem5326954) (@lem5326952)). Qed.
Lemma lem5326956 : term117 = True.
Proof. exact (TRANS (@lem5326951) (@lem5326955)). Qed.
Lemma lem5326957 : True = term117.
Proof. exact (SYM (@lem5326956)). Qed.
Lemma lem5326958 : term117.
Proof. exact (EQ_MP (@lem5326957) (@lem0)). Qed.
Lemma lem5326959 : term543.
Proof. exact (@lem5326948 (@lem5326958)). Qed.
Lemma lem5326961 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5326962 : term117 = term118.
Proof. exact (@lem5326961 (NUMERAL 0) term72). Qed.
Lemma lem5326963 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5326964 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5326965 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5326964 h1) (fun h1 : term118 = True => @lem5326963)). Qed.
Lemma lem5326966 : term118 = True.
Proof. exact (EQ_MP (@lem5326965) (@lem5326963)). Qed.
Lemma lem5326967 : term117 = True.
Proof. exact (TRANS (@lem5326962) (@lem5326966)). Qed.
Lemma lem5326968 : True = term117.
Proof. exact (SYM (@lem5326967)). Qed.
Lemma lem5326969 : term117.
Proof. exact (EQ_MP (@lem5326968) (@lem0)). Qed.
Lemma lem5326970 : term544.
Proof. exact (@lem5326959 (@lem5326969)). Qed.
Lemma lem5326972 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5326973 : term166 = term92.
Proof. exact (@lem5326972 term72 term72). Qed.
Lemma lem5326974 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5326975 : term91 = term72.
Proof. exact (EQ_MP (@lem5326974) (@lem940073)). Qed.
Lemma lem5326976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5326977 : term92 = term78.
Proof. exact (MK_COMB (@lem5326976) (@lem5326975)). Qed.
Lemma lem5326978 : term166 = term78.
Proof. exact (TRANS (@lem5326973) (@lem5326977)). Qed.
Lemma lem5326980 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5326981 : term88 = term89.
Proof. exact (@lem5326980 term72 term72). Qed.
Lemma lem5326982 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5326983 : term91 = term72.
Proof. exact (EQ_MP (@lem5326982) (@lem940073)). Qed.
Lemma lem5326984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5326985 : term92 = term78.
Proof. exact (MK_COMB (@lem5326984) (@lem5326983)). Qed.
Lemma lem5326986 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5326987 : term89 = term66.
Proof. exact (MK_COMB (@lem5326986) (@lem5326985)). Qed.
Lemma lem5326988 : term88 = term66.
Proof. exact (TRANS (@lem5326981) (@lem5326987)). Qed.
Lemma lem5326989 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5326990 : term122 = term123.
Proof. exact (MK_COMB (@lem5326989) (@lem5326988)). Qed.
Lemma lem5326991 : term545 = term539.
Proof. exact (MK_COMB (@lem5326990) (@lem5326978)). Qed.
Lemma lem5326993 (m : nat) : (term254 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5326994 : term539 = term43.
Proof. exact (@lem5326993 term72). Qed.
Lemma lem5326995 : term545 = term43.
Proof. exact (TRANS (@lem5326991) (@lem5326994)). Qed.
Lemma lem5326996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5326997 : term546 = term256.
Proof. exact (MK_COMB (@lem5326996) (@lem5326995)). Qed.
Lemma lem5326998 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5326999 : term547 = term202.
Proof. exact (MK_COMB (@lem5326997) (@lem5326998)). Qed.
Lemma lem5327001 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327002 : term202 = term43.
Proof. exact (@lem5327001 term72). Qed.
Lemma lem5327003 : term547 = term43.
Proof. exact (TRANS (@lem5326999) (@lem5327002)). Qed.
Lemma lem5327005 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327006 : term166 = term92.
Proof. exact (@lem5327005 term72 term72). Qed.
Lemma lem5327007 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327008 : term91 = term72.
Proof. exact (EQ_MP (@lem5327007) (@lem940073)). Qed.
Lemma lem5327009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327010 : term92 = term78.
Proof. exact (MK_COMB (@lem5327009) (@lem5327008)). Qed.
Lemma lem5327011 : term166 = term78.
Proof. exact (TRANS (@lem5327006) (@lem5327010)). Qed.
Lemma lem5327012 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5327013 : term548 = term202.
Proof. exact (MK_COMB (@lem5327012) (@lem5327011)). Qed.
Lemma lem5327015 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327016 : term202 = term43.
Proof. exact (@lem5327015 term72). Qed.
Lemma lem5327017 : term548 = term43.
Proof. exact (TRANS (@lem5327013) (@lem5327016)). Qed.
Lemma lem5327018 : term43 = term548.
Proof. exact (SYM (@lem5327017)). Qed.
Lemma lem5327019 : term547 = term548.
Proof. exact (TRANS (@lem5327003) (@lem5327018)). Qed.
Lemma lem5327020 : term540 = term194.
Proof. exact (@lem5326970 (@lem5327019)). Qed.
Lemma lem5327021 : term539 = term194.
Proof. exact (TRANS (@lem5326936) (@lem5327020)). Qed.
Lemma lem5327023 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5327024 : term194 = term43.
Proof. exact (@lem5327023 term43). Qed.
Lemma lem5327025 : term539 = term43.
Proof. exact (TRANS (@lem5327021) (@lem5327024)). Qed.
Lemma lem5327026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327027 : term549 = term256.
Proof. exact (MK_COMB (@lem5327026) (@lem5327025)). Qed.
Lemma lem5327028 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5327029 (l : real) : (term537 l) = (term270 l).
Proof. exact (MK_COMB (@lem5327027) (@lem5327028 l)). Qed.
Lemma lem5327030 (l : real) : (term536 l) = (term270 l).
Proof. exact (TRANS (@lem5326927 l) (@lem5327029 l)). Qed.
Lemma lem5327031 (l : real) : (term270 l) = term43.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5327032 (l : real) : (term536 l) = term43.
Proof. exact (TRANS (@lem5327030 l) (@lem5327031 l)). Qed.
Lemma lem5327033 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327034 (l : real) : (term550 l) = term272.
Proof. exact (MK_COMB (@lem5327033) (@lem5327032 l)). Qed.
Lemma lem5327035 (y : real) : (term40 y) = (term40 y).
Proof. exact (eq_refl (term40 y)). Qed.
Lemma lem5327036 (l : real) (y : real) : (term535 l y) = (term551 y).
Proof. exact (MK_COMB (@lem5327034 l) (@lem5327035 y)). Qed.
Lemma lem5327037 (l : real) (y : real) : (term534 l y) = (term551 y).
Proof. exact (TRANS (@lem5326926 l y) (@lem5327036 l y)). Qed.
Lemma lem5327038 (y : real) : (term551 y) = (term40 y).
Proof. exact (@lem1982721 (term40 y)). Qed.
Lemma lem5327039 (l : real) (y : real) : (term534 l y) = (term40 y).
Proof. exact (TRANS (@lem5327037 l y) (@lem5327038 y)). Qed.
Lemma lem5327040 (c : real) : (real_add c) = (real_add c).
Proof. exact (eq_refl (real_add c)). Qed.
Lemma lem5327041 (l : real) (c : real) (y : real) : (term533 c l y) = (term38 c y).
Proof. exact (MK_COMB (@lem5327040 c) (@lem5327039 l y)). Qed.
Lemma lem5327042 (l : real) (c : real) (y : real) : (term532 c l y) = (term38 c y).
Proof. exact (TRANS (@lem5326925 c l y) (@lem5327041 l c y)). Qed.
Lemma lem5327043 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5327044 (l : real) (c : real) (y : real) : (term552 c l y) = (term496 c y).
Proof. exact (MK_COMB (@lem5327043) (@lem5327042 l c y)). Qed.
Lemma lem5327045 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5327046 (l : real) (c : real) (y : real) : (term531 c l y) = (term497 c y).
Proof. exact (MK_COMB (@lem5327044 l c y) (@lem5327045)). Qed.
Lemma lem5327047 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term497 c y.
Proof. exact (EQ_MP (@lem5327046 l c y) (@lem5326924 m t c s x l y h1)). Qed.
Lemma lem5327049 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5327050 : term193 = term117.
Proof. exact (@lem5327049 term43 term78). Qed.
Lemma lem5327052 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327053 : term78 = term107.
Proof. exact (@lem5327052 term72). Qed.
Lemma lem5327055 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327056 : term43 = term194.
Proof. exact (@lem5327055 (NUMERAL 0)). Qed.
Lemma lem5327057 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327058 : term195 = term196.
Proof. exact (MK_COMB (@lem5327057) (@lem5327056)). Qed.
Lemma lem5327059 : term117 = term197.
Proof. exact (MK_COMB (@lem5327058) (@lem5327053)). Qed.
Lemma lem5327060 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5327062 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327063 : term117 = term118.
Proof. exact (@lem5327062 (NUMERAL 0) term72). Qed.
Lemma lem5327064 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327065 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327066 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327065 h1) (fun h1 : term118 = True => @lem5327064)). Qed.
Lemma lem5327067 : term118 = True.
Proof. exact (EQ_MP (@lem5327066) (@lem5327064)). Qed.
Lemma lem5327068 : term117 = True.
Proof. exact (TRANS (@lem5327063) (@lem5327067)). Qed.
Lemma lem5327069 : True = term117.
Proof. exact (SYM (@lem5327068)). Qed.
Lemma lem5327070 : term117.
Proof. exact (EQ_MP (@lem5327069) (@lem0)). Qed.
Lemma lem5327071 : term199.
Proof. exact (@lem5327060 (@lem5327070)). Qed.
Lemma lem5327073 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327074 : term117 = term118.
Proof. exact (@lem5327073 (NUMERAL 0) term72). Qed.
Lemma lem5327075 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327076 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327077 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327076 h1) (fun h1 : term118 = True => @lem5327075)). Qed.
Lemma lem5327078 : term118 = True.
Proof. exact (EQ_MP (@lem5327077) (@lem5327075)). Qed.
Lemma lem5327079 : term117 = True.
Proof. exact (TRANS (@lem5327074) (@lem5327078)). Qed.
Lemma lem5327080 : True = term117.
Proof. exact (SYM (@lem5327079)). Qed.
Lemma lem5327081 : term117.
Proof. exact (EQ_MP (@lem5327080) (@lem0)). Qed.
Lemma lem5327082 : term197 = term200.
Proof. exact (@lem5327071 (@lem5327081)). Qed.
Lemma lem5327084 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327085 : term166 = term92.
Proof. exact (@lem5327084 term72 term72). Qed.
Lemma lem5327086 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327087 : term91 = term72.
Proof. exact (EQ_MP (@lem5327086) (@lem940073)). Qed.
Lemma lem5327088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327089 : term92 = term78.
Proof. exact (MK_COMB (@lem5327088) (@lem5327087)). Qed.
Lemma lem5327090 : term166 = term78.
Proof. exact (TRANS (@lem5327085) (@lem5327089)). Qed.
Lemma lem5327092 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327093 : term202 = term43.
Proof. exact (@lem5327092 term72). Qed.
Lemma lem5327094 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327095 : term203 = term195.
Proof. exact (MK_COMB (@lem5327094) (@lem5327093)). Qed.
Lemma lem5327096 : term200 = term117.
Proof. exact (MK_COMB (@lem5327095) (@lem5327090)). Qed.
Lemma lem5327098 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327099 : term117 = term118.
Proof. exact (@lem5327098 (NUMERAL 0) term72). Qed.
Lemma lem5327100 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327101 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327102 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327101 h1) (fun h1 : term118 = True => @lem5327100)). Qed.
Lemma lem5327103 : term118 = True.
Proof. exact (EQ_MP (@lem5327102) (@lem5327100)). Qed.
Lemma lem5327104 : term117 = True.
Proof. exact (TRANS (@lem5327099) (@lem5327103)). Qed.
Lemma lem5327105 : term200 = True.
Proof. exact (TRANS (@lem5327096) (@lem5327104)). Qed.
Lemma lem5327106 : term197 = True.
Proof. exact (TRANS (@lem5327082) (@lem5327105)). Qed.
Lemma lem5327107 : term117 = True.
Proof. exact (TRANS (@lem5327059) (@lem5327106)). Qed.
Lemma lem5327108 : term193 = True.
Proof. exact (TRANS (@lem5327050) (@lem5327107)). Qed.
Lemma lem5327109 : True = term193.
Proof. exact (SYM (@lem5327108)). Qed.
Lemma lem5327110 : term193.
Proof. exact (EQ_MP (@lem5327109) (@lem0)). Qed.
Lemma lem5327111 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term525 c y.
Proof. exact (conj (@lem5327110) (@lem5327047 m t c s x l y h1)). Qed.
Lemma lem5327113 (x : real) (y : real) : term219 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5327114 (c : real) (y : real) : term526 c y.
Proof. exact (@lem5327113 term78 (term38 c y)). Qed.
Lemma lem5327115 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term527 c y.
Proof. exact (@lem5327114 c y (@lem5327111 m t c s x l y h1)). Qed.
Lemma lem5327116 (c : real) (y : real) : (term523 c y) = (term38 c y).
Proof. exact (@lem1982733 (term38 c y)). Qed.
Lemma lem5327117 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5327118 (c : real) (y : real) : (term528 c y) = (term496 c y).
Proof. exact (MK_COMB (@lem5327117) (@lem5327116 c y)). Qed.
Lemma lem5327119 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5327120 (c : real) (y : real) : (term527 c y) = (term497 c y).
Proof. exact (MK_COMB (@lem5327118 c y) (@lem5327119)). Qed.
Lemma lem5327121 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term497 c y.
Proof. exact (EQ_MP (@lem5327120 c y) (@lem5327115 m t c s x l y h1)). Qed.
Lemma lem5327123 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5327124 : term193 = term117.
Proof. exact (@lem5327123 term43 term78). Qed.
Lemma lem5327126 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327127 : term78 = term107.
Proof. exact (@lem5327126 term72). Qed.
Lemma lem5327129 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327130 : term43 = term194.
Proof. exact (@lem5327129 (NUMERAL 0)). Qed.
Lemma lem5327131 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327132 : term195 = term196.
Proof. exact (MK_COMB (@lem5327131) (@lem5327130)). Qed.
Lemma lem5327133 : term117 = term197.
Proof. exact (MK_COMB (@lem5327132) (@lem5327127)). Qed.
Lemma lem5327134 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5327136 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327137 : term117 = term118.
Proof. exact (@lem5327136 (NUMERAL 0) term72). Qed.
Lemma lem5327138 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327139 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327140 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327139 h1) (fun h1 : term118 = True => @lem5327138)). Qed.
Lemma lem5327141 : term118 = True.
Proof. exact (EQ_MP (@lem5327140) (@lem5327138)). Qed.
Lemma lem5327142 : term117 = True.
Proof. exact (TRANS (@lem5327137) (@lem5327141)). Qed.
Lemma lem5327143 : True = term117.
Proof. exact (SYM (@lem5327142)). Qed.
Lemma lem5327144 : term117.
Proof. exact (EQ_MP (@lem5327143) (@lem0)). Qed.
Lemma lem5327145 : term199.
Proof. exact (@lem5327134 (@lem5327144)). Qed.
Lemma lem5327147 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327148 : term117 = term118.
Proof. exact (@lem5327147 (NUMERAL 0) term72). Qed.
Lemma lem5327149 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327150 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327151 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327150 h1) (fun h1 : term118 = True => @lem5327149)). Qed.
Lemma lem5327152 : term118 = True.
Proof. exact (EQ_MP (@lem5327151) (@lem5327149)). Qed.
Lemma lem5327153 : term117 = True.
Proof. exact (TRANS (@lem5327148) (@lem5327152)). Qed.
Lemma lem5327154 : True = term117.
Proof. exact (SYM (@lem5327153)). Qed.
Lemma lem5327155 : term117.
Proof. exact (EQ_MP (@lem5327154) (@lem0)). Qed.
Lemma lem5327156 : term197 = term200.
Proof. exact (@lem5327145 (@lem5327155)). Qed.
Lemma lem5327158 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327159 : term166 = term92.
Proof. exact (@lem5327158 term72 term72). Qed.
Lemma lem5327160 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327161 : term91 = term72.
Proof. exact (EQ_MP (@lem5327160) (@lem940073)). Qed.
Lemma lem5327162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327163 : term92 = term78.
Proof. exact (MK_COMB (@lem5327162) (@lem5327161)). Qed.
Lemma lem5327164 : term166 = term78.
Proof. exact (TRANS (@lem5327159) (@lem5327163)). Qed.
Lemma lem5327166 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327167 : term202 = term43.
Proof. exact (@lem5327166 term72). Qed.
Lemma lem5327168 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327169 : term203 = term195.
Proof. exact (MK_COMB (@lem5327168) (@lem5327167)). Qed.
Lemma lem5327170 : term200 = term117.
Proof. exact (MK_COMB (@lem5327169) (@lem5327164)). Qed.
Lemma lem5327172 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327173 : term117 = term118.
Proof. exact (@lem5327172 (NUMERAL 0) term72). Qed.
Lemma lem5327174 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327175 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327176 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327175 h1) (fun h1 : term118 = True => @lem5327174)). Qed.
Lemma lem5327177 : term118 = True.
Proof. exact (EQ_MP (@lem5327176) (@lem5327174)). Qed.
Lemma lem5327178 : term117 = True.
Proof. exact (TRANS (@lem5327173) (@lem5327177)). Qed.
Lemma lem5327179 : term200 = True.
Proof. exact (TRANS (@lem5327170) (@lem5327178)). Qed.
Lemma lem5327180 : term197 = True.
Proof. exact (TRANS (@lem5327156) (@lem5327179)). Qed.
Lemma lem5327181 : term117 = True.
Proof. exact (TRANS (@lem5327133) (@lem5327180)). Qed.
Lemma lem5327182 : term193 = True.
Proof. exact (TRANS (@lem5327124) (@lem5327181)). Qed.
Lemma lem5327183 : True = term193.
Proof. exact (SYM (@lem5327182)). Qed.
Lemma lem5327184 : term193.
Proof. exact (EQ_MP (@lem5327183) (@lem0)). Qed.
Lemma lem5327185 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term553 c x.
Proof. exact (conj (@lem5327184) (@lem5326693 m t c s x l y h1)). Qed.
Lemma lem5327187 (x : real) (y : real) : term219 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5327188 (c : real) (x : real) : term554 c x.
Proof. exact (@lem5327187 term78 (term39 c x)). Qed.
Lemma lem5327189 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term555 c x.
Proof. exact (@lem5327188 c x (@lem5327185 m t c s x l y h1)). Qed.
Lemma lem5327190 (c : real) (x : real) : (term518 c x) = (term39 c x).
Proof. exact (@lem1982733 (term39 c x)). Qed.
Lemma lem5327191 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5327192 (c : real) (x : real) : (term556 c x) = (term42 c x).
Proof. exact (MK_COMB (@lem5327191) (@lem5327190 c x)). Qed.
Lemma lem5327193 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5327194 (c : real) (x : real) : (term555 c x) = (term44 c x).
Proof. exact (MK_COMB (@lem5327192 c x) (@lem5327193)). Qed.
Lemma lem5327195 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term44 c x.
Proof. exact (EQ_MP (@lem5327194 c x) (@lem5327189 m t c s x l y h1)). Qed.
Lemma lem5327196 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term557 x c y.
Proof. exact (conj (@lem5327195 m t c s x l y h1) (@lem5327121 m t c s x l y h1)). Qed.
Lemma lem5327198 (x : real) (y : real) : term558 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem5327199 (x : real) (c : real) (y : real) : term559 x c y.
Proof. exact (@lem5327198 (term39 c x) (term38 c y)). Qed.
Lemma lem5327200 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term560 x c y.
Proof. exact (@lem5327199 x c y (@lem5327196 m t c s x l y h1)). Qed.
Lemma lem5327201 (c : real) (x : real) (y : real) : (term561 x c y) = (term562 c x y).
Proof. exact (@lem1982753 (term40 c) c x (term40 y)). Qed.
Lemma lem5327202 (c : real) : (term536 c) = (term537 c).
Proof. exact (@lem1982713 term66 c). Qed.
Lemma lem5327204 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327205 : term78 = term107.
Proof. exact (@lem5327204 term72). Qed.
Lemma lem5327207 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5327208 : term66 = term71.
Proof. exact (@lem5327207 term72). Qed.
Lemma lem5327209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327210 : term123 = term538.
Proof. exact (MK_COMB (@lem5327209) (@lem5327208)). Qed.
Lemma lem5327211 : term539 = term540.
Proof. exact (MK_COMB (@lem5327210) (@lem5327205)). Qed.
Lemma lem5327212 : term541.
Proof. exact (@lem1981473 term66 term78 term78 term78 term43 term78). Qed.
Lemma lem5327214 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327215 : term117 = term118.
Proof. exact (@lem5327214 (NUMERAL 0) term72). Qed.
Lemma lem5327216 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327217 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327218 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327217 h1) (fun h1 : term118 = True => @lem5327216)). Qed.
Lemma lem5327219 : term118 = True.
Proof. exact (EQ_MP (@lem5327218) (@lem5327216)). Qed.
Lemma lem5327220 : term117 = True.
Proof. exact (TRANS (@lem5327215) (@lem5327219)). Qed.
Lemma lem5327221 : True = term117.
Proof. exact (SYM (@lem5327220)). Qed.
Lemma lem5327222 : term117.
Proof. exact (EQ_MP (@lem5327221) (@lem0)). Qed.
Lemma lem5327223 : term542.
Proof. exact (@lem5327212 (@lem5327222)). Qed.
Lemma lem5327225 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327226 : term117 = term118.
Proof. exact (@lem5327225 (NUMERAL 0) term72). Qed.
Lemma lem5327227 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327228 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327229 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327228 h1) (fun h1 : term118 = True => @lem5327227)). Qed.
Lemma lem5327230 : term118 = True.
Proof. exact (EQ_MP (@lem5327229) (@lem5327227)). Qed.
Lemma lem5327231 : term117 = True.
Proof. exact (TRANS (@lem5327226) (@lem5327230)). Qed.
Lemma lem5327232 : True = term117.
Proof. exact (SYM (@lem5327231)). Qed.
Lemma lem5327233 : term117.
Proof. exact (EQ_MP (@lem5327232) (@lem0)). Qed.
Lemma lem5327234 : term543.
Proof. exact (@lem5327223 (@lem5327233)). Qed.
Lemma lem5327236 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327237 : term117 = term118.
Proof. exact (@lem5327236 (NUMERAL 0) term72). Qed.
Lemma lem5327238 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327239 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327240 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327239 h1) (fun h1 : term118 = True => @lem5327238)). Qed.
Lemma lem5327241 : term118 = True.
Proof. exact (EQ_MP (@lem5327240) (@lem5327238)). Qed.
Lemma lem5327242 : term117 = True.
Proof. exact (TRANS (@lem5327237) (@lem5327241)). Qed.
Lemma lem5327243 : True = term117.
Proof. exact (SYM (@lem5327242)). Qed.
Lemma lem5327244 : term117.
Proof. exact (EQ_MP (@lem5327243) (@lem0)). Qed.
Lemma lem5327245 : term544.
Proof. exact (@lem5327234 (@lem5327244)). Qed.
Lemma lem5327247 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327248 : term166 = term92.
Proof. exact (@lem5327247 term72 term72). Qed.
Lemma lem5327249 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327250 : term91 = term72.
Proof. exact (EQ_MP (@lem5327249) (@lem940073)). Qed.
Lemma lem5327251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327252 : term92 = term78.
Proof. exact (MK_COMB (@lem5327251) (@lem5327250)). Qed.
Lemma lem5327253 : term166 = term78.
Proof. exact (TRANS (@lem5327248) (@lem5327252)). Qed.
Lemma lem5327255 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5327256 : term88 = term89.
Proof. exact (@lem5327255 term72 term72). Qed.
Lemma lem5327257 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327258 : term91 = term72.
Proof. exact (EQ_MP (@lem5327257) (@lem940073)). Qed.
Lemma lem5327259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327260 : term92 = term78.
Proof. exact (MK_COMB (@lem5327259) (@lem5327258)). Qed.
Lemma lem5327261 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5327262 : term89 = term66.
Proof. exact (MK_COMB (@lem5327261) (@lem5327260)). Qed.
Lemma lem5327263 : term88 = term66.
Proof. exact (TRANS (@lem5327256) (@lem5327262)). Qed.
Lemma lem5327264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327265 : term122 = term123.
Proof. exact (MK_COMB (@lem5327264) (@lem5327263)). Qed.
Lemma lem5327266 : term545 = term539.
Proof. exact (MK_COMB (@lem5327265) (@lem5327253)). Qed.
Lemma lem5327268 (m : nat) : (term254 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5327269 : term539 = term43.
Proof. exact (@lem5327268 term72). Qed.
Lemma lem5327270 : term545 = term43.
Proof. exact (TRANS (@lem5327266) (@lem5327269)). Qed.
Lemma lem5327271 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327272 : term546 = term256.
Proof. exact (MK_COMB (@lem5327271) (@lem5327270)). Qed.
Lemma lem5327273 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5327274 : term547 = term202.
Proof. exact (MK_COMB (@lem5327272) (@lem5327273)). Qed.
Lemma lem5327276 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327277 : term202 = term43.
Proof. exact (@lem5327276 term72). Qed.
Lemma lem5327278 : term547 = term43.
Proof. exact (TRANS (@lem5327274) (@lem5327277)). Qed.
Lemma lem5327280 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327281 : term166 = term92.
Proof. exact (@lem5327280 term72 term72). Qed.
Lemma lem5327282 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327283 : term91 = term72.
Proof. exact (EQ_MP (@lem5327282) (@lem940073)). Qed.
Lemma lem5327284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327285 : term92 = term78.
Proof. exact (MK_COMB (@lem5327284) (@lem5327283)). Qed.
Lemma lem5327286 : term166 = term78.
Proof. exact (TRANS (@lem5327281) (@lem5327285)). Qed.
Lemma lem5327287 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5327288 : term548 = term202.
Proof. exact (MK_COMB (@lem5327287) (@lem5327286)). Qed.
Lemma lem5327290 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327291 : term202 = term43.
Proof. exact (@lem5327290 term72). Qed.
Lemma lem5327292 : term548 = term43.
Proof. exact (TRANS (@lem5327288) (@lem5327291)). Qed.
Lemma lem5327293 : term43 = term548.
Proof. exact (SYM (@lem5327292)). Qed.
Lemma lem5327294 : term547 = term548.
Proof. exact (TRANS (@lem5327278) (@lem5327293)). Qed.
Lemma lem5327295 : term540 = term194.
Proof. exact (@lem5327245 (@lem5327294)). Qed.
Lemma lem5327296 : term539 = term194.
Proof. exact (TRANS (@lem5327211) (@lem5327295)). Qed.
Lemma lem5327298 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5327299 : term194 = term43.
Proof. exact (@lem5327298 term43). Qed.
Lemma lem5327300 : term539 = term43.
Proof. exact (TRANS (@lem5327296) (@lem5327299)). Qed.
Lemma lem5327301 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327302 : term549 = term256.
Proof. exact (MK_COMB (@lem5327301) (@lem5327300)). Qed.
Lemma lem5327303 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5327304 (c : real) : (term537 c) = (term270 c).
Proof. exact (MK_COMB (@lem5327302) (@lem5327303 c)). Qed.
Lemma lem5327305 (c : real) : (term536 c) = (term270 c).
Proof. exact (TRANS (@lem5327202 c) (@lem5327304 c)). Qed.
Lemma lem5327306 (c : real) : (term270 c) = term43.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5327307 (c : real) : (term536 c) = term43.
Proof. exact (TRANS (@lem5327305 c) (@lem5327306 c)). Qed.
Lemma lem5327308 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327309 (c : real) : (term550 c) = term272.
Proof. exact (MK_COMB (@lem5327308) (@lem5327307 c)). Qed.
Lemma lem5327310 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem5327311 (c : real) (x : real) (y : real) : (term562 c x y) = (term563 x y).
Proof. exact (MK_COMB (@lem5327309 c) (@lem5327310 x y)). Qed.
Lemma lem5327312 (c : real) (x : real) (y : real) : (term561 x c y) = (term563 x y).
Proof. exact (TRANS (@lem5327201 c x y) (@lem5327311 c x y)). Qed.
Lemma lem5327313 (x : real) (y : real) : (term563 x y) = (term38 x y).
Proof. exact (@lem1982721 (term38 x y)). Qed.
Lemma lem5327314 (c : real) (x : real) (y : real) : (term561 x c y) = (term38 x y).
Proof. exact (TRANS (@lem5327312 c x y) (@lem5327313 x y)). Qed.
Lemma lem5327315 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5327316 (c : real) (x : real) (y : real) : (term564 x c y) = (term496 x y).
Proof. exact (MK_COMB (@lem5327315) (@lem5327314 c x y)). Qed.
Lemma lem5327317 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5327318 (c : real) (x : real) (y : real) : (term560 x c y) = (term497 x y).
Proof. exact (MK_COMB (@lem5327316 c x y) (@lem5327317)). Qed.
Lemma lem5327319 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term497 x y.
Proof. exact (EQ_MP (@lem5327318 c x y) (@lem5327200 m t c s x l y h1)). Qed.
Lemma lem5327321 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5327322 : term193 = term117.
Proof. exact (@lem5327321 term43 term78). Qed.
Lemma lem5327324 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327325 : term78 = term107.
Proof. exact (@lem5327324 term72). Qed.
Lemma lem5327327 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327328 : term43 = term194.
Proof. exact (@lem5327327 (NUMERAL 0)). Qed.
Lemma lem5327329 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327330 : term195 = term196.
Proof. exact (MK_COMB (@lem5327329) (@lem5327328)). Qed.
Lemma lem5327331 : term117 = term197.
Proof. exact (MK_COMB (@lem5327330) (@lem5327325)). Qed.
Lemma lem5327332 : term198.
Proof. exact (@lem1980255 term43 term78 term78 term78). Qed.
Lemma lem5327334 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327335 : term117 = term118.
Proof. exact (@lem5327334 (NUMERAL 0) term72). Qed.
Lemma lem5327336 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327337 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327338 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327337 h1) (fun h1 : term118 = True => @lem5327336)). Qed.
Lemma lem5327339 : term118 = True.
Proof. exact (EQ_MP (@lem5327338) (@lem5327336)). Qed.
Lemma lem5327340 : term117 = True.
Proof. exact (TRANS (@lem5327335) (@lem5327339)). Qed.
Lemma lem5327341 : True = term117.
Proof. exact (SYM (@lem5327340)). Qed.
Lemma lem5327342 : term117.
Proof. exact (EQ_MP (@lem5327341) (@lem0)). Qed.
Lemma lem5327343 : term199.
Proof. exact (@lem5327332 (@lem5327342)). Qed.
Lemma lem5327345 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327346 : term117 = term118.
Proof. exact (@lem5327345 (NUMERAL 0) term72). Qed.
Lemma lem5327347 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327348 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327349 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327348 h1) (fun h1 : term118 = True => @lem5327347)). Qed.
Lemma lem5327350 : term118 = True.
Proof. exact (EQ_MP (@lem5327349) (@lem5327347)). Qed.
Lemma lem5327351 : term117 = True.
Proof. exact (TRANS (@lem5327346) (@lem5327350)). Qed.
Lemma lem5327352 : True = term117.
Proof. exact (SYM (@lem5327351)). Qed.
Lemma lem5327353 : term117.
Proof. exact (EQ_MP (@lem5327352) (@lem0)). Qed.
Lemma lem5327354 : term197 = term200.
Proof. exact (@lem5327343 (@lem5327353)). Qed.
Lemma lem5327356 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327357 : term166 = term92.
Proof. exact (@lem5327356 term72 term72). Qed.
Lemma lem5327358 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327359 : term91 = term72.
Proof. exact (EQ_MP (@lem5327358) (@lem940073)). Qed.
Lemma lem5327360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327361 : term92 = term78.
Proof. exact (MK_COMB (@lem5327360) (@lem5327359)). Qed.
Lemma lem5327362 : term166 = term78.
Proof. exact (TRANS (@lem5327357) (@lem5327361)). Qed.
Lemma lem5327364 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327365 : term202 = term43.
Proof. exact (@lem5327364 term72). Qed.
Lemma lem5327366 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327367 : term203 = term195.
Proof. exact (MK_COMB (@lem5327366) (@lem5327365)). Qed.
Lemma lem5327368 : term200 = term117.
Proof. exact (MK_COMB (@lem5327367) (@lem5327362)). Qed.
Lemma lem5327370 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327371 : term117 = term118.
Proof. exact (@lem5327370 (NUMERAL 0) term72). Qed.
Lemma lem5327372 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327373 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327374 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327373 h1) (fun h1 : term118 = True => @lem5327372)). Qed.
Lemma lem5327375 : term118 = True.
Proof. exact (EQ_MP (@lem5327374) (@lem5327372)). Qed.
Lemma lem5327376 : term117 = True.
Proof. exact (TRANS (@lem5327371) (@lem5327375)). Qed.
Lemma lem5327377 : term200 = True.
Proof. exact (TRANS (@lem5327368) (@lem5327376)). Qed.
Lemma lem5327378 : term197 = True.
Proof. exact (TRANS (@lem5327354) (@lem5327377)). Qed.
Lemma lem5327379 : term117 = True.
Proof. exact (TRANS (@lem5327331) (@lem5327378)). Qed.
Lemma lem5327380 : term193 = True.
Proof. exact (TRANS (@lem5327322) (@lem5327379)). Qed.
Lemma lem5327381 : True = term193.
Proof. exact (SYM (@lem5327380)). Qed.
Lemma lem5327382 : term193.
Proof. exact (EQ_MP (@lem5327381) (@lem0)). Qed.
Lemma lem5327383 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term525 x y.
Proof. exact (conj (@lem5327382) (@lem5327319 m t c s x l y h1)). Qed.
Lemma lem5327385 (x : real) (y : real) : term219 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5327386 (x : real) (y : real) : term526 x y.
Proof. exact (@lem5327385 term78 (term38 x y)). Qed.
Lemma lem5327387 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term527 x y.
Proof. exact (@lem5327386 x y (@lem5327383 m t c s x l y h1)). Qed.
Lemma lem5327388 (x : real) (y : real) : (term523 x y) = (term38 x y).
Proof. exact (@lem1982733 (term38 x y)). Qed.
Lemma lem5327389 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5327390 (x : real) (y : real) : (term528 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem5327389) (@lem5327388 x y)). Qed.
Lemma lem5327391 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5327392 (x : real) (y : real) : (term527 x y) = (term497 x y).
Proof. exact (MK_COMB (@lem5327390 x y) (@lem5327391)). Qed.
Lemma lem5327393 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term497 x y.
Proof. exact (EQ_MP (@lem5327392 x y) (@lem5327387 m t c s x l y h1)). Qed.
Lemma lem5327394 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term565 x y.
Proof. exact (conj (@lem5327393 m t c s x l y h1) (@lem5326771 m t c s x l y h1)). Qed.
Lemma lem5327396 (x : real) (y : real) : term239 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5327397 (x : real) (y : real) : term566 x y.
Proof. exact (@lem5327396 (term38 x y) (term39 x y)). Qed.
Lemma lem5327398 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term567 x y.
Proof. exact (@lem5327397 x y (@lem5327394 m t c s x l y h1)). Qed.
Lemma lem5327399 (x : real) (y : real) : (term568 x y) = (term569 x y).
Proof. exact (@lem1982753 x (term40 x) (term40 y) y). Qed.
Lemma lem5327400 (x : real) : (term570 x) = (term537 x).
Proof. exact (@lem1982715 term66 x). Qed.
Lemma lem5327402 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327403 : term78 = term107.
Proof. exact (@lem5327402 term72). Qed.
Lemma lem5327405 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5327406 : term66 = term71.
Proof. exact (@lem5327405 term72). Qed.
Lemma lem5327407 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327408 : term123 = term538.
Proof. exact (MK_COMB (@lem5327407) (@lem5327406)). Qed.
Lemma lem5327409 : term539 = term540.
Proof. exact (MK_COMB (@lem5327408) (@lem5327403)). Qed.
Lemma lem5327410 : term541.
Proof. exact (@lem1981473 term66 term78 term78 term78 term43 term78). Qed.
Lemma lem5327412 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327413 : term117 = term118.
Proof. exact (@lem5327412 (NUMERAL 0) term72). Qed.
Lemma lem5327414 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327415 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327416 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327415 h1) (fun h1 : term118 = True => @lem5327414)). Qed.
Lemma lem5327417 : term118 = True.
Proof. exact (EQ_MP (@lem5327416) (@lem5327414)). Qed.
Lemma lem5327418 : term117 = True.
Proof. exact (TRANS (@lem5327413) (@lem5327417)). Qed.
Lemma lem5327419 : True = term117.
Proof. exact (SYM (@lem5327418)). Qed.
Lemma lem5327420 : term117.
Proof. exact (EQ_MP (@lem5327419) (@lem0)). Qed.
Lemma lem5327421 : term542.
Proof. exact (@lem5327410 (@lem5327420)). Qed.
Lemma lem5327423 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327424 : term117 = term118.
Proof. exact (@lem5327423 (NUMERAL 0) term72). Qed.
Lemma lem5327425 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327426 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327427 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327426 h1) (fun h1 : term118 = True => @lem5327425)). Qed.
Lemma lem5327428 : term118 = True.
Proof. exact (EQ_MP (@lem5327427) (@lem5327425)). Qed.
Lemma lem5327429 : term117 = True.
Proof. exact (TRANS (@lem5327424) (@lem5327428)). Qed.
Lemma lem5327430 : True = term117.
Proof. exact (SYM (@lem5327429)). Qed.
Lemma lem5327431 : term117.
Proof. exact (EQ_MP (@lem5327430) (@lem0)). Qed.
Lemma lem5327432 : term543.
Proof. exact (@lem5327421 (@lem5327431)). Qed.
Lemma lem5327434 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327435 : term117 = term118.
Proof. exact (@lem5327434 (NUMERAL 0) term72). Qed.
Lemma lem5327436 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327437 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327438 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327437 h1) (fun h1 : term118 = True => @lem5327436)). Qed.
Lemma lem5327439 : term118 = True.
Proof. exact (EQ_MP (@lem5327438) (@lem5327436)). Qed.
Lemma lem5327440 : term117 = True.
Proof. exact (TRANS (@lem5327435) (@lem5327439)). Qed.
Lemma lem5327441 : True = term117.
Proof. exact (SYM (@lem5327440)). Qed.
Lemma lem5327442 : term117.
Proof. exact (EQ_MP (@lem5327441) (@lem0)). Qed.
Lemma lem5327443 : term544.
Proof. exact (@lem5327432 (@lem5327442)). Qed.
Lemma lem5327445 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327446 : term166 = term92.
Proof. exact (@lem5327445 term72 term72). Qed.
Lemma lem5327447 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327448 : term91 = term72.
Proof. exact (EQ_MP (@lem5327447) (@lem940073)). Qed.
Lemma lem5327449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327450 : term92 = term78.
Proof. exact (MK_COMB (@lem5327449) (@lem5327448)). Qed.
Lemma lem5327451 : term166 = term78.
Proof. exact (TRANS (@lem5327446) (@lem5327450)). Qed.
Lemma lem5327453 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5327454 : term88 = term89.
Proof. exact (@lem5327453 term72 term72). Qed.
Lemma lem5327455 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327456 : term91 = term72.
Proof. exact (EQ_MP (@lem5327455) (@lem940073)). Qed.
Lemma lem5327457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327458 : term92 = term78.
Proof. exact (MK_COMB (@lem5327457) (@lem5327456)). Qed.
Lemma lem5327459 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5327460 : term89 = term66.
Proof. exact (MK_COMB (@lem5327459) (@lem5327458)). Qed.
Lemma lem5327461 : term88 = term66.
Proof. exact (TRANS (@lem5327454) (@lem5327460)). Qed.
Lemma lem5327462 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327463 : term122 = term123.
Proof. exact (MK_COMB (@lem5327462) (@lem5327461)). Qed.
Lemma lem5327464 : term545 = term539.
Proof. exact (MK_COMB (@lem5327463) (@lem5327451)). Qed.
Lemma lem5327466 (m : nat) : (term254 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5327467 : term539 = term43.
Proof. exact (@lem5327466 term72). Qed.
Lemma lem5327468 : term545 = term43.
Proof. exact (TRANS (@lem5327464) (@lem5327467)). Qed.
Lemma lem5327469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327470 : term546 = term256.
Proof. exact (MK_COMB (@lem5327469) (@lem5327468)). Qed.
Lemma lem5327471 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5327472 : term547 = term202.
Proof. exact (MK_COMB (@lem5327470) (@lem5327471)). Qed.
Lemma lem5327474 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327475 : term202 = term43.
Proof. exact (@lem5327474 term72). Qed.
Lemma lem5327476 : term547 = term43.
Proof. exact (TRANS (@lem5327472) (@lem5327475)). Qed.
Lemma lem5327478 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327479 : term166 = term92.
Proof. exact (@lem5327478 term72 term72). Qed.
Lemma lem5327480 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327481 : term91 = term72.
Proof. exact (EQ_MP (@lem5327480) (@lem940073)). Qed.
Lemma lem5327482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327483 : term92 = term78.
Proof. exact (MK_COMB (@lem5327482) (@lem5327481)). Qed.
Lemma lem5327484 : term166 = term78.
Proof. exact (TRANS (@lem5327479) (@lem5327483)). Qed.
Lemma lem5327485 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5327486 : term548 = term202.
Proof. exact (MK_COMB (@lem5327485) (@lem5327484)). Qed.
Lemma lem5327488 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327489 : term202 = term43.
Proof. exact (@lem5327488 term72). Qed.
Lemma lem5327490 : term548 = term43.
Proof. exact (TRANS (@lem5327486) (@lem5327489)). Qed.
Lemma lem5327491 : term43 = term548.
Proof. exact (SYM (@lem5327490)). Qed.
Lemma lem5327492 : term547 = term548.
Proof. exact (TRANS (@lem5327476) (@lem5327491)). Qed.
Lemma lem5327493 : term540 = term194.
Proof. exact (@lem5327443 (@lem5327492)). Qed.
Lemma lem5327494 : term539 = term194.
Proof. exact (TRANS (@lem5327409) (@lem5327493)). Qed.
Lemma lem5327496 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5327497 : term194 = term43.
Proof. exact (@lem5327496 term43). Qed.
Lemma lem5327498 : term539 = term43.
Proof. exact (TRANS (@lem5327494) (@lem5327497)). Qed.
Lemma lem5327499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327500 : term549 = term256.
Proof. exact (MK_COMB (@lem5327499) (@lem5327498)). Qed.
Lemma lem5327501 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5327502 (x : real) : (term537 x) = (term270 x).
Proof. exact (MK_COMB (@lem5327500) (@lem5327501 x)). Qed.
Lemma lem5327503 (x : real) : (term570 x) = (term270 x).
Proof. exact (TRANS (@lem5327400 x) (@lem5327502 x)). Qed.
Lemma lem5327504 (x : real) : (term270 x) = term43.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5327505 (x : real) : (term570 x) = term43.
Proof. exact (TRANS (@lem5327503 x) (@lem5327504 x)). Qed.
Lemma lem5327506 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327507 (x : real) : (term571 x) = term272.
Proof. exact (MK_COMB (@lem5327506) (@lem5327505 x)). Qed.
Lemma lem5327508 (y : real) : (term536 y) = (term537 y).
Proof. exact (@lem1982713 term66 y). Qed.
Lemma lem5327510 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327511 : term78 = term107.
Proof. exact (@lem5327510 term72). Qed.
Lemma lem5327513 (x : nat) : (term69 x) = (term70 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5327514 : term66 = term71.
Proof. exact (@lem5327513 term72). Qed.
Lemma lem5327515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327516 : term123 = term538.
Proof. exact (MK_COMB (@lem5327515) (@lem5327514)). Qed.
Lemma lem5327517 : term539 = term540.
Proof. exact (MK_COMB (@lem5327516) (@lem5327511)). Qed.
Lemma lem5327518 : term541.
Proof. exact (@lem1981473 term66 term78 term78 term78 term43 term78). Qed.
Lemma lem5327520 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327521 : term117 = term118.
Proof. exact (@lem5327520 (NUMERAL 0) term72). Qed.
Lemma lem5327522 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327523 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327524 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327523 h1) (fun h1 : term118 = True => @lem5327522)). Qed.
Lemma lem5327525 : term118 = True.
Proof. exact (EQ_MP (@lem5327524) (@lem5327522)). Qed.
Lemma lem5327526 : term117 = True.
Proof. exact (TRANS (@lem5327521) (@lem5327525)). Qed.
Lemma lem5327527 : True = term117.
Proof. exact (SYM (@lem5327526)). Qed.
Lemma lem5327528 : term117.
Proof. exact (EQ_MP (@lem5327527) (@lem0)). Qed.
Lemma lem5327529 : term542.
Proof. exact (@lem5327518 (@lem5327528)). Qed.
Lemma lem5327531 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327532 : term117 = term118.
Proof. exact (@lem5327531 (NUMERAL 0) term72). Qed.
Lemma lem5327533 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327534 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327535 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327534 h1) (fun h1 : term118 = True => @lem5327533)). Qed.
Lemma lem5327536 : term118 = True.
Proof. exact (EQ_MP (@lem5327535) (@lem5327533)). Qed.
Lemma lem5327537 : term117 = True.
Proof. exact (TRANS (@lem5327532) (@lem5327536)). Qed.
Lemma lem5327538 : True = term117.
Proof. exact (SYM (@lem5327537)). Qed.
Lemma lem5327539 : term117.
Proof. exact (EQ_MP (@lem5327538) (@lem0)). Qed.
Lemma lem5327540 : term543.
Proof. exact (@lem5327529 (@lem5327539)). Qed.
Lemma lem5327542 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327543 : term117 = term118.
Proof. exact (@lem5327542 (NUMERAL 0) term72). Qed.
Lemma lem5327544 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327545 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327546 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327545 h1) (fun h1 : term118 = True => @lem5327544)). Qed.
Lemma lem5327547 : term118 = True.
Proof. exact (EQ_MP (@lem5327546) (@lem5327544)). Qed.
Lemma lem5327548 : term117 = True.
Proof. exact (TRANS (@lem5327543) (@lem5327547)). Qed.
Lemma lem5327549 : True = term117.
Proof. exact (SYM (@lem5327548)). Qed.
Lemma lem5327550 : term117.
Proof. exact (EQ_MP (@lem5327549) (@lem0)). Qed.
Lemma lem5327551 : term544.
Proof. exact (@lem5327540 (@lem5327550)). Qed.
Lemma lem5327553 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327554 : term166 = term92.
Proof. exact (@lem5327553 term72 term72). Qed.
Lemma lem5327555 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327556 : term91 = term72.
Proof. exact (EQ_MP (@lem5327555) (@lem940073)). Qed.
Lemma lem5327557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327558 : term92 = term78.
Proof. exact (MK_COMB (@lem5327557) (@lem5327556)). Qed.
Lemma lem5327559 : term166 = term78.
Proof. exact (TRANS (@lem5327554) (@lem5327558)). Qed.
Lemma lem5327561 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5327562 : term88 = term89.
Proof. exact (@lem5327561 term72 term72). Qed.
Lemma lem5327563 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327564 : term91 = term72.
Proof. exact (EQ_MP (@lem5327563) (@lem940073)). Qed.
Lemma lem5327565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327566 : term92 = term78.
Proof. exact (MK_COMB (@lem5327565) (@lem5327564)). Qed.
Lemma lem5327567 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5327568 : term89 = term66.
Proof. exact (MK_COMB (@lem5327567) (@lem5327566)). Qed.
Lemma lem5327569 : term88 = term66.
Proof. exact (TRANS (@lem5327562) (@lem5327568)). Qed.
Lemma lem5327570 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5327571 : term122 = term123.
Proof. exact (MK_COMB (@lem5327570) (@lem5327569)). Qed.
Lemma lem5327572 : term545 = term539.
Proof. exact (MK_COMB (@lem5327571) (@lem5327559)). Qed.
Lemma lem5327574 (m : nat) : (term254 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5327575 : term539 = term43.
Proof. exact (@lem5327574 term72). Qed.
Lemma lem5327576 : term545 = term43.
Proof. exact (TRANS (@lem5327572) (@lem5327575)). Qed.
Lemma lem5327577 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327578 : term546 = term256.
Proof. exact (MK_COMB (@lem5327577) (@lem5327576)). Qed.
Lemma lem5327579 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem5327580 : term547 = term202.
Proof. exact (MK_COMB (@lem5327578) (@lem5327579)). Qed.
Lemma lem5327582 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327583 : term202 = term43.
Proof. exact (@lem5327582 term72). Qed.
Lemma lem5327584 : term547 = term43.
Proof. exact (TRANS (@lem5327580) (@lem5327583)). Qed.
Lemma lem5327586 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5327587 : term166 = term92.
Proof. exact (@lem5327586 term72 term72). Qed.
Lemma lem5327588 : (term90 = (BIT1 0)) = (term91 = term72).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5327589 : term91 = term72.
Proof. exact (EQ_MP (@lem5327588) (@lem940073)). Qed.
Lemma lem5327590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5327591 : term92 = term78.
Proof. exact (MK_COMB (@lem5327590) (@lem5327589)). Qed.
Lemma lem5327592 : term166 = term78.
Proof. exact (TRANS (@lem5327587) (@lem5327591)). Qed.
Lemma lem5327593 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem5327594 : term548 = term202.
Proof. exact (MK_COMB (@lem5327593) (@lem5327592)). Qed.
Lemma lem5327596 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327597 : term202 = term43.
Proof. exact (@lem5327596 term72). Qed.
Lemma lem5327598 : term548 = term43.
Proof. exact (TRANS (@lem5327594) (@lem5327597)). Qed.
Lemma lem5327599 : term43 = term548.
Proof. exact (SYM (@lem5327598)). Qed.
Lemma lem5327600 : term547 = term548.
Proof. exact (TRANS (@lem5327584) (@lem5327599)). Qed.
Lemma lem5327601 : term540 = term194.
Proof. exact (@lem5327551 (@lem5327600)). Qed.
Lemma lem5327602 : term539 = term194.
Proof. exact (TRANS (@lem5327517) (@lem5327601)). Qed.
Lemma lem5327604 (x : real) : (term268 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5327605 : term194 = term43.
Proof. exact (@lem5327604 term43). Qed.
Lemma lem5327606 : term539 = term43.
Proof. exact (TRANS (@lem5327602) (@lem5327605)). Qed.
Lemma lem5327607 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5327608 : term549 = term256.
Proof. exact (MK_COMB (@lem5327607) (@lem5327606)). Qed.
Lemma lem5327609 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5327610 (y : real) : (term537 y) = (term270 y).
Proof. exact (MK_COMB (@lem5327608) (@lem5327609 y)). Qed.
Lemma lem5327611 (y : real) : (term536 y) = (term270 y).
Proof. exact (TRANS (@lem5327508 y) (@lem5327610 y)). Qed.
Lemma lem5327612 (y : real) : (term270 y) = term43.
Proof. exact (@lem1982719 y). Qed.
Lemma lem5327613 (y : real) : (term536 y) = term43.
Proof. exact (TRANS (@lem5327611 y) (@lem5327612 y)). Qed.
Lemma lem5327614 (x : real) (y : real) : (term569 x y) = term288.
Proof. exact (MK_COMB (@lem5327507 x) (@lem5327613 y)). Qed.
Lemma lem5327615 (x : real) (y : real) : (term568 x y) = term288.
Proof. exact (TRANS (@lem5327399 x y) (@lem5327614 x y)). Qed.
Lemma lem5327616 : term288 = term43.
Proof. exact (@lem1982721 term43). Qed.
Lemma lem5327617 (x : real) (y : real) : (term568 x y) = term43.
Proof. exact (TRANS (@lem5327615 x y) (@lem5327616)). Qed.
Lemma lem5327618 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5327619 (x : real) (y : real) : (term572 x y) = term290.
Proof. exact (MK_COMB (@lem5327618) (@lem5327617 x y)). Qed.
Lemma lem5327620 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem5327621 (x : real) (y : real) : (term567 x y) = term291.
Proof. exact (MK_COMB (@lem5327619 x y) (@lem5327620)). Qed.
Lemma lem5327622 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term291.
Proof. exact (EQ_MP (@lem5327621 x y) (@lem5327398 m t c s x l y h1)). Qed.
Lemma lem5327624 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5327625 : term291 = term292.
Proof. exact (@lem5327624 term43 term43). Qed.
Lemma lem5327627 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327628 : term43 = term194.
Proof. exact (@lem5327627 (NUMERAL 0)). Qed.
Lemma lem5327630 (x : nat) : (real_of_num x) = (term106 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5327631 : term43 = term194.
Proof. exact (@lem5327630 (NUMERAL 0)). Qed.
Lemma lem5327632 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327633 : term195 = term196.
Proof. exact (MK_COMB (@lem5327632) (@lem5327631)). Qed.
Lemma lem5327634 : term292 = term293.
Proof. exact (MK_COMB (@lem5327633) (@lem5327628)). Qed.
Lemma lem5327635 : term294.
Proof. exact (@lem1980255 term43 term78 term43 term78). Qed.
Lemma lem5327637 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327638 : term117 = term118.
Proof. exact (@lem5327637 (NUMERAL 0) term72). Qed.
Lemma lem5327639 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327640 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327641 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327640 h1) (fun h1 : term118 = True => @lem5327639)). Qed.
Lemma lem5327642 : term118 = True.
Proof. exact (EQ_MP (@lem5327641) (@lem5327639)). Qed.
Lemma lem5327643 : term117 = True.
Proof. exact (TRANS (@lem5327638) (@lem5327642)). Qed.
Lemma lem5327644 : True = term117.
Proof. exact (SYM (@lem5327643)). Qed.
Lemma lem5327645 : term117.
Proof. exact (EQ_MP (@lem5327644) (@lem0)). Qed.
Lemma lem5327646 : term295.
Proof. exact (@lem5327635 (@lem5327645)). Qed.
Lemma lem5327648 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327649 : term117 = term118.
Proof. exact (@lem5327648 (NUMERAL 0) term72). Qed.
Lemma lem5327650 : term119 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5327651 (h1 : term119 = (BIT1 0)) : term118 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5327652 : (term119 = (BIT1 0)) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = (BIT1 0) => @lem5327651 h1) (fun h1 : term118 = True => @lem5327650)). Qed.
Lemma lem5327653 : term118 = True.
Proof. exact (EQ_MP (@lem5327652) (@lem5327650)). Qed.
Lemma lem5327654 : term117 = True.
Proof. exact (TRANS (@lem5327649) (@lem5327653)). Qed.
Lemma lem5327655 : True = term117.
Proof. exact (SYM (@lem5327654)). Qed.
Lemma lem5327656 : term117.
Proof. exact (EQ_MP (@lem5327655) (@lem0)). Qed.
Lemma lem5327657 : term293 = term296.
Proof. exact (@lem5327646 (@lem5327656)). Qed.
Lemma lem5327659 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327660 : term202 = term43.
Proof. exact (@lem5327659 term72). Qed.
Lemma lem5327662 (x : nat) : (term201 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5327663 : term202 = term43.
Proof. exact (@lem5327662 term72). Qed.
Lemma lem5327664 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5327665 : term203 = term195.
Proof. exact (MK_COMB (@lem5327664) (@lem5327663)). Qed.
Lemma lem5327666 : term296 = term292.
Proof. exact (MK_COMB (@lem5327665) (@lem5327660)). Qed.
Lemma lem5327668 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5327669 : term292 = term297.
Proof. exact (@lem5327668 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5327670 : term297 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5327671 : term292 = False.
Proof. exact (TRANS (@lem5327669) (@lem5327670)). Qed.
Lemma lem5327672 : term296 = False.
Proof. exact (TRANS (@lem5327666) (@lem5327671)). Qed.
Lemma lem5327673 : term293 = False.
Proof. exact (TRANS (@lem5327657) (@lem5327672)). Qed.
Lemma lem5327674 : term292 = False.
Proof. exact (TRANS (@lem5327634) (@lem5327673)). Qed.
Lemma lem5327675 : term291 = False.
Proof. exact (TRANS (@lem5327625) (@lem5327674)). Qed.
Lemma lem5327676 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : False.
Proof. exact (EQ_MP (@lem5327675) (@lem5327622 m t c s x l y h1)). Qed.
Lemma lem5327678 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : term514 m t c s x l y.
Proof. exact (h1). Qed.
Lemma lem5327679 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : (term514 m t c s x l y) = False.
Proof. exact (prop_ext (fun h2 : term514 m t c s x l y => @lem5327676 m t c s x l y h1) (fun h2 : False => @lem5327678 m t c s x l y h1)). Qed.
Lemma lem5327680 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term514 m t c s x l y) : False.
Proof. exact (EQ_MP (@lem5327679 m t c s x l y h1) (@lem5327678 m t c s x l y h1)). Qed.
Lemma lem5327681 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) (h1 : term494 m t c s x y l) : term494 m t c s x y l.
Proof. exact (h1). Qed.
Lemma lem5327682 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) (h1 : term494 m t c s x y l) : term514 m t c s x l y.
Proof. exact (EQ_MP (@lem5326675 m t c s x l y) (@lem5327681 m t c s x y l h1)). Qed.
Lemma lem5327683 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) (h1 : term494 m t c s x y l) : (term514 m t c s x l y) = False.
Proof. exact (prop_ext (fun h2 : term514 m t c s x l y => @lem5327680 m t c s x l y h2) (fun h2 : False => @lem5327682 m t c s x y l h1)). Qed.
Lemma lem5327684 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) (h1 : term494 m t c s x y l) : False.
Proof. exact (EQ_MP (@lem5327683 m t c s x y l h1) (@lem5327682 m t c s x y l h1)). Qed.
Lemma lem5327685 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : term573 m t c s x y l.
Proof. exact (fun h0 : term494 m t c s x y l => @lem5327684 m t c s x y l h0). Qed.
Lemma lem5327686 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : term574 m t c s x y l.
Proof. exact (@lem1386578 (term575 m t c s x y l)). Qed.
Lemma lem5327689 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (y : real) (l : real) : term575 m t c s x y l.
Proof. exact (@lem5327686 m t c s x y l (@lem5327685 m t c s x y l)). Qed.
Lemma lem5327690 (m : real) (t : real -> Prop) (c : real) (x : real) (y : real) (l : real) (s : real -> Prop) (h1 : term12 s) : term495 m t c s x y l.
Proof. exact (@lem5327689 m t c s x y l (@lem5323666 s h1)). Qed.
Lemma lem5327691 (m : real) (c : real) (x : real) (y : real) (l : real) (s : real -> Prop) (t : real -> Prop) (h1 : term12 s) (h2 : term12 t) : term491 m t c s x y l.
Proof. exact (@lem5327690 m t c x y l s h1 (@lem5323698 t h2)). Qed.
Lemma lem5327692 (c : real) (x : real) (y : real) (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) : term487 m t c s x y l.
Proof. exact (@lem5327691 m c x y l s t h1 h2 (@lem5323709 m l h3)). Qed.
Lemma lem5327693 (x : real) (y : real) (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : real_lt l c) : term483 m t c s x y l.
Proof. exact (@lem5327692 c x y s t m l h1 h2 h3 (@lem5323713 l c h4)). Qed.
Lemma lem5327694 (x : real) (y : real) (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : real_lt c m) (h5 : real_lt l c) : term479 t c s x y l.
Proof. exact (@lem5327693 x y s t m l c h1 h2 h3 h5 (@lem5323712 c m h4)). Qed.
Lemma lem5327695 (y : real) (s : real -> Prop) (x : real) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : @IN real x t) (h5 : real_lt c m) (h6 : real_lt l c) : term475 c s x y l.
Proof. exact (@lem5327694 x y s t m l c h1 h2 h3 h5 h6 (@lem5325412 x t h4)). Qed.
Lemma lem5327696 (y : real) (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : @IN real x t) (h5 : real_lt c m) (h6 : real_lt c x) (h7 : real_lt l c) : term471 s x y l.
Proof. exact (@lem5327695 y s x t m l c h1 h2 h3 h4 h5 h7 (@lem5325411 c x h6)). Qed.
Lemma lem5327697 (t : real -> Prop) (y : real) (s : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : @IN real x t) (h5 : @IN real y s) (h6 : real_lt c m) (h7 : real_lt c x) (h8 : real_lt l c) : term467 x y l.
Proof. exact (@lem5327696 y s t m x l c h1 h2 h3 h4 h6 h7 h8 (@lem5325416 y s h5)). Qed.
Lemma lem5327698 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : @IN real x t) (h5 : @IN real y s) (h6 : real_le x y) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : term3 y l.
Proof. exact (@lem5327697 t y s m x l c h1 h2 h3 h4 h5 h7 h8 h9 (@lem5325415 x y h6)). Qed.
Lemma lem5327699 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 m l) (h4 : @IN real x t) (h5 : @IN real y s) (h6 : real_le x y) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : term455 s y l.
Proof. exact (EQ_MP (@lem5326345 l y s h5) (@lem5327698 t s y m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9)). Qed.
Lemma lem5327700 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le x y) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : False.
Proof. exact (@lem5327699 t s y m x l c h2 h3 h4 h5 h6 h7 h8 h9 h10 (@lem5326271 y s l h1)). Qed.
Lemma lem5327701 (s : real -> Prop) (x : real) (y : real) (h1 : term330 s x y) : real_le x y.
Proof. exact (proj2 (@lem5325414 s x y h1)). Qed.
Lemma lem5327702 (s : real -> Prop) (x : real) (y : real) (h1 : term330 s x y) : @IN real y s.
Proof. exact (proj1 (@lem5325414 s x y h1)). Qed.
Lemma lem5327703 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le x y) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : (real_le x y) = False.
Proof. exact (prop_ext (fun h11 : real_le x y => @lem5327700 t s y m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem5325415 x y h7)). Qed.
Lemma lem5327704 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le x y) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327703 t s y m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem5325415 x y h7)). Qed.
Lemma lem5327705 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le x y) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : (@IN real y s) = False.
Proof. exact (prop_ext (fun h11 : @IN real y s => @lem5327704 t s y m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem5325416 y s h6)). Qed.
Lemma lem5327706 (t : real -> Prop) (s : real -> Prop) (y : real) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le x y) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327705 t s y m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem5325416 y s h6)). Qed.
Lemma lem5327707 (t : real -> Prop) (y : real) (s : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : term330 s x y) (h6 : @IN real x t) (h7 : @IN real y s) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : (real_le x y) = False.
Proof. exact (prop_ext (fun h11 : real_le x y => @lem5327706 t s y m x l c h1 h2 h3 h4 h6 h7 h11 h8 h9 h10) (fun h11 : False => @lem5327701 s x y h5)). Qed.
Lemma lem5327708 (t : real -> Prop) (y : real) (s : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : term330 s x y) (h6 : @IN real x t) (h7 : @IN real y s) (h8 : real_lt c m) (h9 : real_lt c x) (h10 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327707 t y s m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem5327701 s x y h5)). Qed.
Lemma lem5327709 (s : real -> Prop) (y : real) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : term330 s x y) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : (@IN real y s) = False.
Proof. exact (prop_ext (fun h10 : @IN real y s => @lem5327708 t y s m x l c h1 h2 h3 h4 h5 h6 h10 h7 h8 h9) (fun h10 : False => @lem5327702 s x y h5)). Qed.
Lemma lem5327710 (s : real -> Prop) (y : real) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 m l) (h5 : term330 s x y) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327709 s y t m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5327702 s x y h5)). Qed.
Lemma lem5327711 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term329 s x) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : False.
Proof. exact (ex_elim (@lem5325413 s x h2) (fun y : real => fun h0 : term356 s x y => @lem5327710 s y t m x l c h1 h3 h4 h5 h0 h6 h7 h8 h9)). Qed.
Lemma lem5327712 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : (term329 s x) = False.
Proof. exact (prop_ext (fun h10 : term329 s x => @lem5327711 s t m x l c h1 h10 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5326268 s x t h2 h6)). Qed.
Lemma lem5327713 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327712 s t m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5326268 s x t h2 h6)). Qed.
Lemma lem5327714 (t : real -> Prop) (c : real) (x : real) (h1 : term319 t c x) : real_lt c x.
Proof. exact (proj2 (@lem5325410 t c x h1)). Qed.
Lemma lem5327715 (t : real -> Prop) (c : real) (x : real) (h1 : term319 t c x) : @IN real x t.
Proof. exact (proj1 (@lem5325410 t c x h1)). Qed.
Lemma lem5327716 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : (real_lt c x) = False.
Proof. exact (prop_ext (fun h10 : real_lt c x => @lem5327713 s t m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5325411 c x h8)). Qed.
Lemma lem5327717 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327716 s t m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5325411 c x h8)). Qed.
Lemma lem5327718 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h10 : @IN real x t => @lem5327717 s t m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5325412 x t h6)). Qed.
Lemma lem5327719 (s : real -> Prop) (t : real -> Prop) (m : real) (x : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : @IN real x t) (h7 : real_lt c m) (h8 : real_lt c x) (h9 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327718 s t m x l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5325412 x t h6)). Qed.
Lemma lem5327720 (s : real -> Prop) (x : real) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : term319 t c x) (h7 : @IN real x t) (h8 : real_lt c m) (h9 : real_lt l c) : (real_lt c x) = False.
Proof. exact (prop_ext (fun h10 : real_lt c x => @lem5327719 s t m x l c h1 h2 h3 h4 h5 h7 h8 h10 h9) (fun h10 : False => @lem5327714 t c x h6)). Qed.
Lemma lem5327721 (s : real -> Prop) (x : real) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : term319 t c x) (h7 : @IN real x t) (h8 : real_lt c m) (h9 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327720 s x t m l c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5327714 t c x h6)). Qed.
Lemma lem5327722 (s : real -> Prop) (t : real -> Prop) (x : real) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : term319 t c x) (h7 : real_lt c m) (h8 : real_lt l c) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h9 : @IN real x t => @lem5327721 s x t m l c h1 h2 h3 h4 h5 h6 h9 h7 h8) (fun h9 : False => @lem5327715 t c x h6)). Qed.
Lemma lem5327723 (s : real -> Prop) (t : real -> Prop) (x : real) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : term319 t c x) (h7 : real_lt c m) (h8 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327722 s t x m l c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5327715 t c x h6)). Qed.
Lemma lem5327724 (x : real) (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : real_lt c m) (h7 : real_lt l c) : term576 t c x.
Proof. exact (fun h0 : term319 t c x => @lem5327723 s t x m l c h1 h2 h3 h4 h5 h0 h6 h7). Qed.
Lemma lem5327725 (t : real -> Prop) (c : real) (x : real) : (term576 t c x) = (term325 t c x).
Proof. exact (@lem69 (term319 t c x)). Qed.
Lemma lem5327726 (x : real) (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : real_lt c m) (h7 : real_lt l c) : term325 t c x.
Proof. exact (EQ_MP (@lem5327725 t c x) (@lem5327724 x s t m l c h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5327732 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : real_lt c m) (h7 : real_lt l c) : term328 t c.
Proof. exact (fun x : real => @lem5327726 x s t m l c h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem5327733 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 m l) (h6 : real_lt c m) (h7 : real_lt l c) : term307 m t c.
Proof. exact (EQ_MP (@lem5325407 t c m h6) (@lem5327732 s t m l c h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5327734 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : real_lt c m) (h8 : real_lt l c) : False.
Proof. exact (@lem5327733 s t m l c h1 h2 h4 h5 h6 h7 h8 (@lem5325294 c m t h3)). Qed.
Lemma lem5327735 (l : real) (c : real) (m : real) (h1 : term18 l c m) : real_lt c m.
Proof. exact (proj2 (@lem5323711 l c m h1)). Qed.
Lemma lem5327736 (l : real) (c : real) (m : real) (h1 : term18 l c m) : real_lt l c.
Proof. exact (proj1 (@lem5323711 l c m h1)). Qed.
Lemma lem5327737 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : real_lt c m) (h8 : real_lt l c) : (real_lt c m) = False.
Proof. exact (prop_ext (fun h9 : real_lt c m => @lem5327734 s t m l c h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5323712 c m h7)). Qed.
Lemma lem5327738 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : real_lt c m) (h8 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327737 s t m l c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5323712 c m h7)). Qed.
Lemma lem5327739 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : real_lt c m) (h8 : real_lt l c) : (real_lt l c) = False.
Proof. exact (prop_ext (fun h9 : real_lt l c => @lem5327738 s t m l c h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5323713 l c h8)). Qed.
Lemma lem5327740 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : real_lt c m) (h8 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327739 s t m l c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5323713 l c h8)). Qed.
Lemma lem5327741 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : term18 l c m) (h8 : real_lt l c) : (real_lt c m) = False.
Proof. exact (prop_ext (fun h9 : real_lt c m => @lem5327740 s t m l c h1 h2 h3 h4 h5 h6 h9 h8) (fun h9 : False => @lem5327735 l c m h7)). Qed.
Lemma lem5327742 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : term18 l c m) (h8 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5327741 s t m l c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5327735 l c m h7)). Qed.
Lemma lem5327743 (s : real -> Prop) (t : real -> Prop) (l : real) (c : real) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : term18 l c m) : (real_lt l c) = False.
Proof. exact (prop_ext (fun h8 : real_lt l c => @lem5327742 s t m l c h1 h2 h3 h4 h5 h6 h7 h8) (fun h8 : False => @lem5327736 l c m h7)). Qed.
Lemma lem5327744 (s : real -> Prop) (t : real -> Prop) (l : real) (c : real) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) (h7 : term18 l c m) : False.
Proof. exact (EQ_MP (@lem5327743 s t l c m h1 h2 h3 h4 h5 h6 h7) (@lem5327736 l c m h7)). Qed.
Lemma lem5327745 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term17 l m) (h5 : term12 s) (h6 : term12 t) (h7 : term3 m l) : False.
Proof. exact (ex_elim (@lem5323710 l m h4) (fun c : real => fun h0 : term301 l m c => @lem5327744 s t l c m h1 h2 h3 h5 h6 h7 h0)). Qed.
Lemma lem5327746 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) : (term17 l m) = False.
Proof. exact (prop_ext (fun h7 : term17 l m => @lem5327745 s t m l h1 h2 h3 h7 h4 h5 h6) (fun h7 : False => @lem5325291 s t m l h4 h5 h6)). Qed.
Lemma lem5327747 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 m l) : False.
Proof. exact (EQ_MP (@lem5327746 s t m l h1 h2 h3 h4 h5 h6) (@lem5325291 s t m l h4 h5 h6)). Qed.
Lemma lem5327748 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : term16 m l.
Proof. exact (fun h0 : term3 m l => @lem5327747 s t m l h1 h2 h3 h4 h5 h0). Qed.
Lemma lem5327749 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : real_le m l.
Proof. exact (EQ_MP (@lem5323704 m l) (@lem5327748 l m s t h1 h2 h3 h4 h5)). Qed.
Lemma lem5327750 (t : real -> Prop) (m : real) (h1 : has_sup t m) : term11 m t.
Proof. exact (proj2 (@lem5323696 t m h1)). Qed.
Lemma lem5327751 (t : real -> Prop) (m : real) (h1 : has_sup t m) : term12 t.
Proof. exact (proj1 (@lem5323696 t m h1)). Qed.
Lemma lem5327752 (m : real) (t : real -> Prop) (h1 : term11 m t) : term14 m t.
Proof. exact (proj2 (@lem5323697 m t h1)). Qed.
Lemma lem5327754 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : (term14 m t) = (real_le m l).
Proof. exact (prop_ext (fun h6 : term14 m t => @lem5327749 l m s t h1 h2 h3 h4 h5) (fun h6 : real_le m l => @lem5323699 m t h3)). Qed.
Lemma lem5327755 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : real_le m l.
Proof. exact (EQ_MP (@lem5327754 l m s t h1 h2 h3 h4 h5) (@lem5323699 m t h3)). Qed.
Lemma lem5327756 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : (term14 m t) = (real_le m l).
Proof. exact (prop_ext (fun h6 : term14 m t => @lem5327755 l m s t h1 h2 h6 h3 h4) (fun h6 : real_le m l => @lem5327752 m t h5)). Qed.
Lemma lem5327757 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : real_le m l.
Proof. exact (EQ_MP (@lem5327756 l s m t h1 h2 h3 h4 h5) (@lem5327752 m t h5)). Qed.
Lemma lem5327758 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : (term12 t) = (real_le m l).
Proof. exact (prop_ext (fun h6 : term12 t => @lem5327757 l s m t h1 h2 h3 h4 h5) (fun h6 : real_le m l => @lem5323698 t h4)). Qed.
Lemma lem5327759 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : real_le m l.
Proof. exact (EQ_MP (@lem5327758 l s m t h1 h2 h3 h4 h5) (@lem5323698 t h4)). Qed.
Lemma lem5327760 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : has_sup t m) : (term11 m t) = (real_le m l).
Proof. exact (prop_ext (fun h6 : term11 m t => @lem5327759 l s m t h1 h2 h3 h4 h6) (fun h6 : real_le m l => @lem5327750 t m h5)). Qed.
Lemma lem5327761 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327760 l s t m h1 h2 h3 h4 h5) (@lem5327750 t m h5)). Qed.
Lemma lem5327762 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_sup t m) : (term12 t) = (real_le m l).
Proof. exact (prop_ext (fun h5 : term12 t => @lem5327761 l s t m h1 h2 h3 h5 h4) (fun h5 : real_le m l => @lem5327751 t m h4)). Qed.
Lemma lem5327763 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327762 l s t m h1 h2 h3 h4) (@lem5327751 t m h4)). Qed.
Lemma lem5327764 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term11 l s.
Proof. exact (proj2 (@lem5323664 s l h1)). Qed.
Lemma lem5327765 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term12 s.
Proof. exact (proj1 (@lem5323664 s l h1)). Qed.
Lemma lem5327767 (l : real) (s : real -> Prop) (h1 : term11 l s) : term13 s l.
Proof. exact (proj1 (@lem5323665 l s h1)). Qed.
Lemma lem5327768 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_sup t m) : (term13 s l) = (real_le m l).
Proof. exact (prop_ext (fun h5 : term13 s l => @lem5327763 l s t m h1 h2 h3 h4) (fun h5 : real_le m l => @lem5323668 s l h1)). Qed.
Lemma lem5327769 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327768 l s t m h1 h2 h3 h4) (@lem5323668 s l h1)). Qed.
Lemma lem5327770 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_sup t m) : (term13 s l) = (real_le m l).
Proof. exact (prop_ext (fun h5 : term13 s l => @lem5327769 l s t m h5 h1 h2 h4) (fun h5 : real_le m l => @lem5327767 l s h3)). Qed.
Lemma lem5327771 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327770 l s t m h1 h2 h3 h4) (@lem5327767 l s h3)). Qed.
Lemma lem5327772 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_sup t m) : (term12 s) = (real_le m l).
Proof. exact (prop_ext (fun h5 : term12 s => @lem5327771 l s t m h1 h2 h3 h4) (fun h5 : real_le m l => @lem5323666 s h2)). Qed.
Lemma lem5327773 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327772 l s t m h1 h2 h3 h4) (@lem5323666 s h2)). Qed.
Lemma lem5327774 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : has_sup s l) (h4 : has_sup t m) : (term11 l s) = (real_le m l).
Proof. exact (prop_ext (fun h5 : term11 l s => @lem5327773 l s t m h1 h2 h5 h4) (fun h5 : real_le m l => @lem5327764 s l h3)). Qed.
Lemma lem5327775 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : has_sup s l) (h4 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327774 s l t m h1 h2 h3 h4) (@lem5327764 s l h3)). Qed.
Lemma lem5327776 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_sup s l) (h3 : has_sup t m) : (term12 s) = (real_le m l).
Proof. exact (prop_ext (fun h4 : term12 s => @lem5327775 s l t m h1 h4 h2 h3) (fun h4 : real_le m l => @lem5327765 s l h2)). Qed.
Lemma lem5327777 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_sup s l) (h3 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327776 s l t m h1 h2 h3) (@lem5327765 s l h2)). Qed.
Lemma lem5327778 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : term9 m t s.
Proof. exact (proj2 (@lem5323633 l m t s h1)). Qed.
Lemma lem5327779 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : has_sup s l.
Proof. exact (proj1 (@lem5323633 l m t s h1)). Qed.
Lemma lem5327780 (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term9 m t s) : term10 t s.
Proof. exact (proj2 (@lem5323634 m t s h1)). Qed.
Lemma lem5327781 (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term9 m t s) : has_sup t m.
Proof. exact (proj1 (@lem5323634 m t s h1)). Qed.
Lemma lem5327782 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_sup s l) (h3 : has_sup t m) : (term10 t s) = (real_le m l).
Proof. exact (prop_ext (fun h4 : term10 t s => @lem5327777 s l t m h1 h2 h3) (fun h4 : real_le m l => @lem5323636 t s h1)). Qed.
Lemma lem5327783 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_sup s l) (h3 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327782 s l t m h1 h2 h3) (@lem5323636 t s h1)). Qed.
Lemma lem5327784 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_sup s l) (h3 : has_sup t m) : (has_sup t m) = (real_le m l).
Proof. exact (prop_ext (fun h4 : has_sup t m => @lem5327783 s l t m h1 h2 h3) (fun h4 : real_le m l => @lem5323637 t m h3)). Qed.
Lemma lem5327785 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_sup s l) (h3 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327784 s l t m h1 h2 h3) (@lem5323637 t m h3)). Qed.
Lemma lem5327786 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term9 m t s) (h2 : has_sup s l) (h3 : has_sup t m) : (term10 t s) = (real_le m l).
Proof. exact (prop_ext (fun h4 : term10 t s => @lem5327785 s l t m h4 h2 h3) (fun h4 : real_le m l => @lem5327780 m t s h1)). Qed.
Lemma lem5327787 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term9 m t s) (h2 : has_sup s l) (h3 : has_sup t m) : real_le m l.
Proof. exact (EQ_MP (@lem5327786 s l t m h1 h2 h3) (@lem5327780 m t s h1)). Qed.
Lemma lem5327788 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_sup s l) : (has_sup t m) = (real_le m l).
Proof. exact (prop_ext (fun h3 : has_sup t m => @lem5327787 s l t m h1 h2 h3) (fun h3 : real_le m l => @lem5327781 m t s h1)). Qed.
Lemma lem5327789 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_sup s l) : real_le m l.
Proof. exact (EQ_MP (@lem5327788 m t s l h1 h2) (@lem5327781 m t s h1)). Qed.
Lemma lem5327790 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_sup s l) : (has_sup s l) = (real_le m l).
Proof. exact (prop_ext (fun h3 : has_sup s l => @lem5327789 m t s l h1 h2) (fun h3 : real_le m l => @lem5323635 s l h2)). Qed.
Lemma lem5327791 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_sup s l) : real_le m l.
Proof. exact (EQ_MP (@lem5327790 m t s l h1 h2) (@lem5323635 s l h2)). Qed.
Lemma lem5327792 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term8 l m t s) (h2 : has_sup s l) : (term9 m t s) = (real_le m l).
Proof. exact (prop_ext (fun h3 : term9 m t s => @lem5327791 m t s l h3 h2) (fun h3 : real_le m l => @lem5327778 l m t s h1)). Qed.
Lemma lem5327793 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term8 l m t s) (h2 : has_sup s l) : real_le m l.
Proof. exact (EQ_MP (@lem5327792 m t s l h1 h2) (@lem5327778 l m t s h1)). Qed.
Lemma lem5327794 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : (has_sup s l) = (real_le m l).
Proof. exact (prop_ext (fun h2 : has_sup s l => @lem5327793 m t s l h1 h2) (fun h2 : real_le m l => @lem5327779 l m t s h1)). Qed.
Lemma lem5327795 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : real_le m l.
Proof. exact (EQ_MP (@lem5327794 l m t s h1) (@lem5327779 l m t s h1)). Qed.
Lemma lem5327796 (t : real -> Prop) (s : real -> Prop) (m : real) (l : real) : term577 t s m l.
Proof. exact (fun h0 : term8 l m t s => @lem5327795 l m t s h0). Qed.
Lemma lem5327802 (t : real -> Prop) (s : real -> Prop) (l : real) : term578 t s l.
Proof. exact (fun m : real => @lem5327796 t s m l). Qed.
Lemma lem5327808 (t : real -> Prop) (s : real -> Prop) : term579 t s.
Proof. exact (fun l : real => @lem5327802 t s l). Qed.
Lemma lem5327814 (s : real -> Prop) : term580 s.
Proof. exact (fun t : real -> Prop => @lem5327808 t s). Qed.
Lemma lem5327820 : term581.
Proof. exact (fun s : real -> Prop => @lem5327814 s). Qed.
