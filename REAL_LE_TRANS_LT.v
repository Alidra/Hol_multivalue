Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_TRANS_LT_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367765_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19367_spec.
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
Require Import thm1982723_spec.
Require Import thm1982725_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1982796_spec.
Require Import thm1982797_spec.
Require Import thm1988285_spec.
Require Import thm1988287_spec.
Require Import thm1988295_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm32_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem1992619 (y : real) (x : real) (z : real) : (term0 y x z) = (term1 y x z).
Proof. exact (@lem17362 (real_lt y z) (real_lt x z)). Qed.
Lemma lem1992620 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1992621 (y : real) (x : real) : (term4 y x) = (term5 y x).
Proof. exact (@lem1992620 (term6 y x)). Qed.
Lemma lem1992622 (y : real) (x : real) (z : real) : (term7 y x z) = (term8 y x z).
Proof. exact (eq_refl (term7 y x z)). Qed.
Lemma lem1992623 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1992624 (y : real) (x : real) (z : real) : (term9 y x z) = (term0 y x z).
Proof. exact (MK_COMB (@lem1992623) (@lem1992622 y x z)). Qed.
Lemma lem1992625 (y : real) (x : real) (z : real) : (term9 y x z) = (term1 y x z).
Proof. exact (TRANS (@lem1992624 y x z) (@lem1992619 y x z)). Qed.
Lemma lem1992626 (y : real) (x : real) : (term10 y x) = (term11 y x).
Proof. exact (fun_ext (fun z : real => @lem1992625 y x z)). Qed.
Lemma lem1992627 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1992628 (y : real) (x : real) : (term5 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1992627) (@lem1992626 y x)). Qed.
Lemma lem1992629 (y : real) (x : real) : (term4 y x) = (term12 y x).
Proof. exact (TRANS (@lem1992621 y x) (@lem1992628 y x)). Qed.
Lemma lem1992631 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1992632 (y : real) (x : real) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1992631 x y) (@lem1992629 y x)). Qed.
Lemma lem1992633 (y : real) (x : real) : (term16 y x) = (term14 y x).
Proof. exact (@lem17362 (real_le x y) (term17 y x)). Qed.
Lemma lem1992635 (y : real) (x : real) : (term16 y x) = (term15 y x).
Proof. exact (TRANS (@lem1992633 y x) (@lem1992632 y x)). Qed.
Lemma lem1992642 (y : real) (x : real) (z : real) : (term1 y x z) = (term1 y x z).
Proof. exact (eq_refl (term1 y x z)). Qed.
Lemma lem1992643 (y : real) (x : real) : (term11 y x) = (term11 y x).
Proof. exact (fun_ext (fun z : real => @lem1992642 y x z)). Qed.
Lemma lem1992644 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1992645 (y : real) (x : real) : (term12 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1992644) (@lem1992643 y x)). Qed.
Lemma lem1992648 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1992649 (y : real) (x : real) : (term15 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1992648 x y) (@lem1992645 y x)). Qed.
Lemma lem1992650 (y : real) (x : real) : (term16 y x) = (term15 y x).
Proof. exact (TRANS (@lem1992635 y x) (@lem1992649 y x)). Qed.
Lemma lem1992651 (y : real) (x : real) : (real_le x y) = (term18 y x).
Proof. exact (@lem1988287 y x). Qed.
Lemma lem1992657 (y : real) (x : real) : (real_sub y x) = (term19 y x).
Proof. exact (@lem1982792 y x). Qed.
Lemma lem1992662 (x : real) (y : real) : (term19 y x) = (term20 x y).
Proof. exact (@lem1982761 (term21 x) y). Qed.
Lemma lem1992664 (x : real) (y : real) : (real_sub y x) = (term20 x y).
Proof. exact (TRANS (@lem1992657 y x) (@lem1992662 x y)). Qed.
Lemma lem1992665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1992666 (x : real) (y : real) : (term22 y x) = (term23 x y).
Proof. exact (MK_COMB (@lem1992665) (@lem1992664 x y)). Qed.
Lemma lem1992667 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992668 (x : real) (y : real) : (term18 y x) = (term25 x y).
Proof. exact (MK_COMB (@lem1992666 x y) (@lem1992667)). Qed.
Lemma lem1992669 (x : real) (y : real) : (real_le x y) = (term25 x y).
Proof. exact (TRANS (@lem1992651 y x) (@lem1992668 x y)). Qed.
Lemma lem1992670 (z : real) (y : real) : (real_lt y z) = (term26 z y).
Proof. exact (@lem1988285 z y). Qed.
Lemma lem1992676 (z : real) (y : real) : (real_sub z y) = (term19 z y).
Proof. exact (@lem1982792 z y). Qed.
Lemma lem1992681 (y : real) (z : real) : (term19 z y) = (term20 y z).
Proof. exact (@lem1982761 (term21 y) z). Qed.
Lemma lem1992683 (y : real) (z : real) : (real_sub z y) = (term20 y z).
Proof. exact (TRANS (@lem1992676 z y) (@lem1992681 y z)). Qed.
Lemma lem1992684 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1992685 (y : real) (z : real) : (term27 z y) = (term28 y z).
Proof. exact (MK_COMB (@lem1992684) (@lem1992683 y z)). Qed.
Lemma lem1992686 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992687 (y : real) (z : real) : (term26 z y) = (term29 y z).
Proof. exact (MK_COMB (@lem1992685 y z) (@lem1992686)). Qed.
Lemma lem1992688 (y : real) (z : real) : (real_lt y z) = (term29 y z).
Proof. exact (TRANS (@lem1992670 z y) (@lem1992687 y z)). Qed.
Lemma lem1992689 (x : real) (z : real) : (term30 x z) = (term18 x z).
Proof. exact (@lem1988295 x z). Qed.
Lemma lem1992702 (x : real) (z : real) : (real_sub x z) = (term19 x z).
Proof. exact (@lem1982792 x z). Qed.
Lemma lem1992703 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1992704 (x : real) (z : real) : (term22 x z) = (term31 x z).
Proof. exact (MK_COMB (@lem1992703) (@lem1992702 x z)). Qed.
Lemma lem1992705 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992706 (x : real) (z : real) : (term18 x z) = (term32 x z).
Proof. exact (MK_COMB (@lem1992704 x z) (@lem1992705)). Qed.
Lemma lem1992707 (x : real) (z : real) : (term30 x z) = (term32 x z).
Proof. exact (TRANS (@lem1992689 x z) (@lem1992706 x z)). Qed.
Lemma lem1992708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1992709 (y : real) (z : real) : (term33 y z) = (term34 y z).
Proof. exact (MK_COMB (@lem1992708) (@lem1992688 y z)). Qed.
Lemma lem1992710 (y : real) (x : real) (z : real) : (term1 y x z) = (term35 y x z).
Proof. exact (MK_COMB (@lem1992709 y z) (@lem1992707 x z)). Qed.
Lemma lem1992711 (y : real) (x : real) : (term11 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1992710 y x z)). Qed.
Lemma lem1992712 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1992713 (y : real) (x : real) : (term12 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1992712) (@lem1992711 y x)). Qed.
Lemma lem1992714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1992715 (x : real) (y : real) : (term13 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1992714) (@lem1992669 x y)). Qed.
Lemma lem1992716 (y : real) (x : real) : (term15 y x) = (term39 y x).
Proof. exact (MK_COMB (@lem1992715 x y) (@lem1992713 y x)). Qed.
Lemma lem1992717 (y : real) (x : real) : (term16 y x) = (term39 y x).
Proof. exact (TRANS (@lem1992650 y x) (@lem1992716 y x)). Qed.
Lemma lem1992768 {A : Type'} (P : Prop) (Q : A -> Prop) : (term40 A P Q) = (term41 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1992769 (P : Prop) (Q : real -> Prop) : (term42 P Q) = (term43 P Q).
Proof. exact (@lem1992768 real P Q). Qed.
Lemma lem1992770 (y : real) (x : real) : (term44 y x) = (term45 y x).
Proof. exact (@lem1992769 (term25 x y) (term36 y x)). Qed.
Lemma lem1992771 (y : real) (x : real) (z : real) : (term46 y x z) = (term35 y x z).
Proof. exact (eq_refl (term46 y x z)). Qed.
Lemma lem1992772 (y : real) (x : real) : (term47 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1992771 y x z)). Qed.
Lemma lem1992773 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1992774 (y : real) (x : real) : (term48 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1992773) (@lem1992772 y x)). Qed.
Lemma lem1992775 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1992776 (y : real) (x : real) : (term44 y x) = (term39 y x).
Proof. exact (MK_COMB (@lem1992775 x y) (@lem1992774 y x)). Qed.
Lemma lem1992777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1992778 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (MK_COMB (@lem1992777) (@lem1992776 y x)). Qed.
Lemma lem1992779 (y : real) (x : real) (z : real) : (term46 y x z) = (term35 y x z).
Proof. exact (eq_refl (term46 y x z)). Qed.
Lemma lem1992780 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1992781 (y : real) (x : real) (z : real) : (term51 y x z) = (term52 y x z).
Proof. exact (MK_COMB (@lem1992780 x y) (@lem1992779 y x z)). Qed.
Lemma lem1992782 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (fun_ext (fun z : real => @lem1992781 y x z)). Qed.
Lemma lem1992783 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1992784 (y : real) (x : real) : (term45 y x) = (term55 y x).
Proof. exact (MK_COMB (@lem1992783) (@lem1992782 y x)). Qed.
Lemma lem1992785 (y : real) (x : real) : ((term44 y x) = (term45 y x)) = ((term39 y x) = (term55 y x)).
Proof. exact (MK_COMB (@lem1992778 y x) (@lem1992784 y x)). Qed.
Lemma lem1992787 (y : real) (x : real) : (term39 y x) = (term55 y x).
Proof. exact (EQ_MP (@lem1992785 y x) (@lem1992770 y x)). Qed.
Lemma lem1992790 (y : real) (x : real) : (term16 y x) = (term55 y x).
Proof. exact (TRANS (@lem1992717 y x) (@lem1992787 y x)). Qed.
Lemma lem1992803 (y : real) (x : real) (z : real) : (term52 y x z) = (term52 y x z).
Proof. exact (eq_refl (term52 y x z)). Qed.
Lemma lem1992804 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (fun_ext (fun z : real => @lem1992803 y x z)). Qed.
Lemma lem1992805 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1992806 (y : real) (x : real) : (term55 y x) = (term55 y x).
Proof. exact (MK_COMB (@lem1992805) (@lem1992804 y x)). Qed.
Lemma lem1992807 (y : real) (x : real) : (term16 y x) = (term55 y x).
Proof. exact (TRANS (@lem1992790 y x) (@lem1992806 y x)). Qed.
Lemma lem1992811 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term52 y x z.
Proof. exact (h1). Qed.
Lemma lem1992812 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term35 y x z.
Proof. exact (proj2 (@lem1992811 y x z h1)). Qed.
Lemma lem1992813 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term25 x y.
Proof. exact (proj1 (@lem1992811 y x z h1)). Qed.
Lemma lem1992814 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term32 x z.
Proof. exact (proj2 (@lem1992812 y x z h1)). Qed.
Lemma lem1992815 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term29 y z.
Proof. exact (proj1 (@lem1992812 y x z h1)). Qed.
Lemma lem1992817 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992818 : term56 = term57.
Proof. exact (@lem1992817 term24 term58). Qed.
Lemma lem1992820 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992821 : term58 = term60.
Proof. exact (@lem1992820 term61). Qed.
Lemma lem1992823 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992824 : term24 = term62.
Proof. exact (@lem1992823 (NUMERAL 0)). Qed.
Lemma lem1992825 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992826 : term63 = term64.
Proof. exact (MK_COMB (@lem1992825) (@lem1992824)). Qed.
Lemma lem1992827 : term57 = term65.
Proof. exact (MK_COMB (@lem1992826) (@lem1992821)). Qed.
Lemma lem1992828 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1992830 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992831 : term57 = term68.
Proof. exact (@lem1992830 (NUMERAL 0) term61). Qed.
Lemma lem1992832 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992833 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992834 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992833 h1) (fun h1 : term68 = True => @lem1992832)). Qed.
Lemma lem1992835 : term68 = True.
Proof. exact (EQ_MP (@lem1992834) (@lem1992832)). Qed.
Lemma lem1992836 : term57 = True.
Proof. exact (TRANS (@lem1992831) (@lem1992835)). Qed.
Lemma lem1992837 : True = term57.
Proof. exact (SYM (@lem1992836)). Qed.
Lemma lem1992838 : term57.
Proof. exact (EQ_MP (@lem1992837) (@lem0)). Qed.
Lemma lem1992839 : term70.
Proof. exact (@lem1992828 (@lem1992838)). Qed.
Lemma lem1992841 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992842 : term57 = term68.
Proof. exact (@lem1992841 (NUMERAL 0) term61). Qed.
Lemma lem1992843 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992844 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992845 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992844 h1) (fun h1 : term68 = True => @lem1992843)). Qed.
Lemma lem1992846 : term68 = True.
Proof. exact (EQ_MP (@lem1992845) (@lem1992843)). Qed.
Lemma lem1992847 : term57 = True.
Proof. exact (TRANS (@lem1992842) (@lem1992846)). Qed.
Lemma lem1992848 : True = term57.
Proof. exact (SYM (@lem1992847)). Qed.
Lemma lem1992849 : term57.
Proof. exact (EQ_MP (@lem1992848) (@lem0)). Qed.
Lemma lem1992850 : term65 = term71.
Proof. exact (@lem1992839 (@lem1992849)). Qed.
Lemma lem1992852 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992853 : term74 = term75.
Proof. exact (@lem1992852 term61 term61). Qed.
Lemma lem1992854 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992855 : term77 = term61.
Proof. exact (EQ_MP (@lem1992854) (@lem940073)). Qed.
Lemma lem1992856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992857 : term75 = term58.
Proof. exact (MK_COMB (@lem1992856) (@lem1992855)). Qed.
Lemma lem1992858 : term74 = term58.
Proof. exact (TRANS (@lem1992853) (@lem1992857)). Qed.
Lemma lem1992860 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992861 : term79 = term24.
Proof. exact (@lem1992860 term61). Qed.
Lemma lem1992862 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992863 : term80 = term63.
Proof. exact (MK_COMB (@lem1992862) (@lem1992861)). Qed.
Lemma lem1992864 : term71 = term57.
Proof. exact (MK_COMB (@lem1992863) (@lem1992858)). Qed.
Lemma lem1992866 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992867 : term57 = term68.
Proof. exact (@lem1992866 (NUMERAL 0) term61). Qed.
Lemma lem1992868 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992869 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992870 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992869 h1) (fun h1 : term68 = True => @lem1992868)). Qed.
Lemma lem1992871 : term68 = True.
Proof. exact (EQ_MP (@lem1992870) (@lem1992868)). Qed.
Lemma lem1992872 : term57 = True.
Proof. exact (TRANS (@lem1992867) (@lem1992871)). Qed.
Lemma lem1992873 : term71 = True.
Proof. exact (TRANS (@lem1992864) (@lem1992872)). Qed.
Lemma lem1992874 : term65 = True.
Proof. exact (TRANS (@lem1992850) (@lem1992873)). Qed.
Lemma lem1992875 : term57 = True.
Proof. exact (TRANS (@lem1992827) (@lem1992874)). Qed.
Lemma lem1992876 : term56 = True.
Proof. exact (TRANS (@lem1992818) (@lem1992875)). Qed.
Lemma lem1992877 : True = term56.
Proof. exact (SYM (@lem1992876)). Qed.
Lemma lem1992878 : term56.
Proof. exact (EQ_MP (@lem1992877) (@lem0)). Qed.
Lemma lem1992879 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term81 x y.
Proof. exact (conj (@lem1992878) (@lem1992813 y x z h1)). Qed.
Lemma lem1992881 (x : real) (y : real) : term82 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1992882 (x : real) (y : real) : term83 x y.
Proof. exact (@lem1992881 term58 (term20 x y)). Qed.
Lemma lem1992883 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term84 x y.
Proof. exact (@lem1992882 x y (@lem1992879 y x z h1)). Qed.
Lemma lem1992884 (x : real) (y : real) : (term85 x y) = (term20 x y).
Proof. exact (@lem1982733 (term20 x y)). Qed.
Lemma lem1992885 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1992886 (x : real) (y : real) : (term86 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1992885) (@lem1992884 x y)). Qed.
Lemma lem1992887 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992888 (x : real) (y : real) : (term84 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1992886 x y) (@lem1992887)). Qed.
Lemma lem1992889 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term25 x y.
Proof. exact (EQ_MP (@lem1992888 x y) (@lem1992883 y x z h1)). Qed.
Lemma lem1992891 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992892 : term56 = term57.
Proof. exact (@lem1992891 term24 term58). Qed.
Lemma lem1992894 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992895 : term58 = term60.
Proof. exact (@lem1992894 term61). Qed.
Lemma lem1992897 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992898 : term24 = term62.
Proof. exact (@lem1992897 (NUMERAL 0)). Qed.
Lemma lem1992899 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992900 : term63 = term64.
Proof. exact (MK_COMB (@lem1992899) (@lem1992898)). Qed.
Lemma lem1992901 : term57 = term65.
Proof. exact (MK_COMB (@lem1992900) (@lem1992895)). Qed.
Lemma lem1992902 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1992904 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992905 : term57 = term68.
Proof. exact (@lem1992904 (NUMERAL 0) term61). Qed.
Lemma lem1992906 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992907 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992908 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992907 h1) (fun h1 : term68 = True => @lem1992906)). Qed.
Lemma lem1992909 : term68 = True.
Proof. exact (EQ_MP (@lem1992908) (@lem1992906)). Qed.
Lemma lem1992910 : term57 = True.
Proof. exact (TRANS (@lem1992905) (@lem1992909)). Qed.
Lemma lem1992911 : True = term57.
Proof. exact (SYM (@lem1992910)). Qed.
Lemma lem1992912 : term57.
Proof. exact (EQ_MP (@lem1992911) (@lem0)). Qed.
Lemma lem1992913 : term70.
Proof. exact (@lem1992902 (@lem1992912)). Qed.
Lemma lem1992915 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992916 : term57 = term68.
Proof. exact (@lem1992915 (NUMERAL 0) term61). Qed.
Lemma lem1992917 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992918 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992919 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992918 h1) (fun h1 : term68 = True => @lem1992917)). Qed.
Lemma lem1992920 : term68 = True.
Proof. exact (EQ_MP (@lem1992919) (@lem1992917)). Qed.
Lemma lem1992921 : term57 = True.
Proof. exact (TRANS (@lem1992916) (@lem1992920)). Qed.
Lemma lem1992922 : True = term57.
Proof. exact (SYM (@lem1992921)). Qed.
Lemma lem1992923 : term57.
Proof. exact (EQ_MP (@lem1992922) (@lem0)). Qed.
Lemma lem1992924 : term65 = term71.
Proof. exact (@lem1992913 (@lem1992923)). Qed.
Lemma lem1992926 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1992927 : term74 = term75.
Proof. exact (@lem1992926 term61 term61). Qed.
Lemma lem1992928 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1992929 : term77 = term61.
Proof. exact (EQ_MP (@lem1992928) (@lem940073)). Qed.
Lemma lem1992930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1992931 : term75 = term58.
Proof. exact (MK_COMB (@lem1992930) (@lem1992929)). Qed.
Lemma lem1992932 : term74 = term58.
Proof. exact (TRANS (@lem1992927) (@lem1992931)). Qed.
Lemma lem1992934 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1992935 : term79 = term24.
Proof. exact (@lem1992934 term61). Qed.
Lemma lem1992936 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992937 : term80 = term63.
Proof. exact (MK_COMB (@lem1992936) (@lem1992935)). Qed.
Lemma lem1992938 : term71 = term57.
Proof. exact (MK_COMB (@lem1992937) (@lem1992932)). Qed.
Lemma lem1992940 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992941 : term57 = term68.
Proof. exact (@lem1992940 (NUMERAL 0) term61). Qed.
Lemma lem1992942 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992943 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992944 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992943 h1) (fun h1 : term68 = True => @lem1992942)). Qed.
Lemma lem1992945 : term68 = True.
Proof. exact (EQ_MP (@lem1992944) (@lem1992942)). Qed.
Lemma lem1992946 : term57 = True.
Proof. exact (TRANS (@lem1992941) (@lem1992945)). Qed.
Lemma lem1992947 : term71 = True.
Proof. exact (TRANS (@lem1992938) (@lem1992946)). Qed.
Lemma lem1992948 : term65 = True.
Proof. exact (TRANS (@lem1992924) (@lem1992947)). Qed.
Lemma lem1992949 : term57 = True.
Proof. exact (TRANS (@lem1992901) (@lem1992948)). Qed.
Lemma lem1992950 : term56 = True.
Proof. exact (TRANS (@lem1992892) (@lem1992949)). Qed.
Lemma lem1992951 : True = term56.
Proof. exact (SYM (@lem1992950)). Qed.
Lemma lem1992952 : term56.
Proof. exact (EQ_MP (@lem1992951) (@lem0)). Qed.
Lemma lem1992953 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term87 x z.
Proof. exact (conj (@lem1992952) (@lem1992814 y x z h1)). Qed.
Lemma lem1992955 (x : real) (y : real) : term82 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1992956 (x : real) (z : real) : term88 x z.
Proof. exact (@lem1992955 term58 (term19 x z)). Qed.
Lemma lem1992957 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term89 x z.
Proof. exact (@lem1992956 x z (@lem1992953 y x z h1)). Qed.
Lemma lem1992958 (x : real) (z : real) : (term90 x z) = (term19 x z).
Proof. exact (@lem1982733 (term19 x z)). Qed.
Lemma lem1992959 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1992960 (x : real) (z : real) : (term91 x z) = (term31 x z).
Proof. exact (MK_COMB (@lem1992959) (@lem1992958 x z)). Qed.
Lemma lem1992961 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1992962 (x : real) (z : real) : (term89 x z) = (term32 x z).
Proof. exact (MK_COMB (@lem1992960 x z) (@lem1992961)). Qed.
Lemma lem1992963 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term32 x z.
Proof. exact (EQ_MP (@lem1992962 x z) (@lem1992957 y x z h1)). Qed.
Lemma lem1992965 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1992966 : term56 = term57.
Proof. exact (@lem1992965 term24 term58). Qed.
Lemma lem1992968 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992969 : term58 = term60.
Proof. exact (@lem1992968 term61). Qed.
Lemma lem1992971 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1992972 : term24 = term62.
Proof. exact (@lem1992971 (NUMERAL 0)). Qed.
Lemma lem1992973 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1992974 : term63 = term64.
Proof. exact (MK_COMB (@lem1992973) (@lem1992972)). Qed.
Lemma lem1992975 : term57 = term65.
Proof. exact (MK_COMB (@lem1992974) (@lem1992969)). Qed.
Lemma lem1992976 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1992978 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992979 : term57 = term68.
Proof. exact (@lem1992978 (NUMERAL 0) term61). Qed.
Lemma lem1992980 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992981 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992982 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992981 h1) (fun h1 : term68 = True => @lem1992980)). Qed.
Lemma lem1992983 : term68 = True.
Proof. exact (EQ_MP (@lem1992982) (@lem1992980)). Qed.
Lemma lem1992984 : term57 = True.
Proof. exact (TRANS (@lem1992979) (@lem1992983)). Qed.
Lemma lem1992985 : True = term57.
Proof. exact (SYM (@lem1992984)). Qed.
Lemma lem1992986 : term57.
Proof. exact (EQ_MP (@lem1992985) (@lem0)). Qed.
Lemma lem1992987 : term70.
Proof. exact (@lem1992976 (@lem1992986)). Qed.
Lemma lem1992989 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1992990 : term57 = term68.
Proof. exact (@lem1992989 (NUMERAL 0) term61). Qed.
Lemma lem1992991 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1992992 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1992993 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1992992 h1) (fun h1 : term68 = True => @lem1992991)). Qed.
Lemma lem1992994 : term68 = True.
Proof. exact (EQ_MP (@lem1992993) (@lem1992991)). Qed.
Lemma lem1992995 : term57 = True.
Proof. exact (TRANS (@lem1992990) (@lem1992994)). Qed.
Lemma lem1992996 : True = term57.
Proof. exact (SYM (@lem1992995)). Qed.
Lemma lem1992997 : term57.
Proof. exact (EQ_MP (@lem1992996) (@lem0)). Qed.
Lemma lem1992998 : term65 = term71.
Proof. exact (@lem1992987 (@lem1992997)). Qed.
Lemma lem1993000 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993001 : term74 = term75.
Proof. exact (@lem1993000 term61 term61). Qed.
Lemma lem1993002 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993003 : term77 = term61.
Proof. exact (EQ_MP (@lem1993002) (@lem940073)). Qed.
Lemma lem1993004 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993005 : term75 = term58.
Proof. exact (MK_COMB (@lem1993004) (@lem1993003)). Qed.
Lemma lem1993006 : term74 = term58.
Proof. exact (TRANS (@lem1993001) (@lem1993005)). Qed.
Lemma lem1993008 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993009 : term79 = term24.
Proof. exact (@lem1993008 term61). Qed.
Lemma lem1993010 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1993011 : term80 = term63.
Proof. exact (MK_COMB (@lem1993010) (@lem1993009)). Qed.
Lemma lem1993012 : term71 = term57.
Proof. exact (MK_COMB (@lem1993011) (@lem1993006)). Qed.
Lemma lem1993014 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993015 : term57 = term68.
Proof. exact (@lem1993014 (NUMERAL 0) term61). Qed.
Lemma lem1993016 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993017 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993018 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993017 h1) (fun h1 : term68 = True => @lem1993016)). Qed.
Lemma lem1993019 : term68 = True.
Proof. exact (EQ_MP (@lem1993018) (@lem1993016)). Qed.
Lemma lem1993020 : term57 = True.
Proof. exact (TRANS (@lem1993015) (@lem1993019)). Qed.
Lemma lem1993021 : term71 = True.
Proof. exact (TRANS (@lem1993012) (@lem1993020)). Qed.
Lemma lem1993022 : term65 = True.
Proof. exact (TRANS (@lem1992998) (@lem1993021)). Qed.
Lemma lem1993023 : term57 = True.
Proof. exact (TRANS (@lem1992975) (@lem1993022)). Qed.
Lemma lem1993024 : term56 = True.
Proof. exact (TRANS (@lem1992966) (@lem1993023)). Qed.
Lemma lem1993025 : True = term56.
Proof. exact (SYM (@lem1993024)). Qed.
Lemma lem1993026 : term56.
Proof. exact (EQ_MP (@lem1993025) (@lem0)). Qed.
Lemma lem1993027 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term92 y z.
Proof. exact (conj (@lem1993026) (@lem1992815 y x z h1)). Qed.
Lemma lem1993029 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1993030 (y : real) (z : real) : term94 y z.
Proof. exact (@lem1993029 term58 (term20 y z)). Qed.
Lemma lem1993031 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term95 y z.
Proof. exact (@lem1993030 y z (@lem1993027 y x z h1)). Qed.
Lemma lem1993032 (y : real) (z : real) : (term85 y z) = (term20 y z).
Proof. exact (@lem1982733 (term20 y z)). Qed.
Lemma lem1993033 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1993034 (y : real) (z : real) : (term96 y z) = (term28 y z).
Proof. exact (MK_COMB (@lem1993033) (@lem1993032 y z)). Qed.
Lemma lem1993035 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1993036 (y : real) (z : real) : (term95 y z) = (term29 y z).
Proof. exact (MK_COMB (@lem1993034 y z) (@lem1993035)). Qed.
Lemma lem1993037 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term29 y z.
Proof. exact (EQ_MP (@lem1993036 y z) (@lem1993031 y x z h1)). Qed.
Lemma lem1993038 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term35 y x z.
Proof. exact (conj (@lem1993037 y x z h1) (@lem1992963 y x z h1)). Qed.
Lemma lem1993040 (x : real) (y : real) : term97 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1993041 (y : real) (x : real) (z : real) : term98 y x z.
Proof. exact (@lem1993040 (term20 y z) (term19 x z)). Qed.
Lemma lem1993042 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term99 y x z.
Proof. exact (@lem1993041 y x z (@lem1993038 y x z h1)). Qed.
Lemma lem1993043 (x : real) (y : real) (z : real) : (term100 y x z) = (term101 x y z).
Proof. exact (@lem1982757 x (term20 y z) (term21 z)). Qed.
Lemma lem1993044 (y : real) (z : real) : (term102 y z) = (term103 y z).
Proof. exact (@lem1982755 (term21 y) z (term21 z)). Qed.
Lemma lem1993045 (z : real) : (term104 z) = (term105 z).
Proof. exact (@lem1982715 term106 z). Qed.
Lemma lem1993047 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993048 : term58 = term60.
Proof. exact (@lem1993047 term61). Qed.
Lemma lem1993050 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1993051 : term106 = term109.
Proof. exact (@lem1993050 term61). Qed.
Lemma lem1993052 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993053 : term110 = term111.
Proof. exact (MK_COMB (@lem1993052) (@lem1993051)). Qed.
Lemma lem1993054 : term112 = term113.
Proof. exact (MK_COMB (@lem1993053) (@lem1993048)). Qed.
Lemma lem1993055 : term114.
Proof. exact (@lem1981473 term106 term58 term58 term58 term24 term58). Qed.
Lemma lem1993057 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993058 : term57 = term68.
Proof. exact (@lem1993057 (NUMERAL 0) term61). Qed.
Lemma lem1993059 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993060 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993061 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993060 h1) (fun h1 : term68 = True => @lem1993059)). Qed.
Lemma lem1993062 : term68 = True.
Proof. exact (EQ_MP (@lem1993061) (@lem1993059)). Qed.
Lemma lem1993063 : term57 = True.
Proof. exact (TRANS (@lem1993058) (@lem1993062)). Qed.
Lemma lem1993064 : True = term57.
Proof. exact (SYM (@lem1993063)). Qed.
Lemma lem1993065 : term57.
Proof. exact (EQ_MP (@lem1993064) (@lem0)). Qed.
Lemma lem1993066 : term115.
Proof. exact (@lem1993055 (@lem1993065)). Qed.
Lemma lem1993068 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993069 : term57 = term68.
Proof. exact (@lem1993068 (NUMERAL 0) term61). Qed.
Lemma lem1993070 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993071 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993072 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993071 h1) (fun h1 : term68 = True => @lem1993070)). Qed.
Lemma lem1993073 : term68 = True.
Proof. exact (EQ_MP (@lem1993072) (@lem1993070)). Qed.
Lemma lem1993074 : term57 = True.
Proof. exact (TRANS (@lem1993069) (@lem1993073)). Qed.
Lemma lem1993075 : True = term57.
Proof. exact (SYM (@lem1993074)). Qed.
Lemma lem1993076 : term57.
Proof. exact (EQ_MP (@lem1993075) (@lem0)). Qed.
Lemma lem1993077 : term116.
Proof. exact (@lem1993066 (@lem1993076)). Qed.
Lemma lem1993079 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993080 : term57 = term68.
Proof. exact (@lem1993079 (NUMERAL 0) term61). Qed.
Lemma lem1993081 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993082 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993083 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993082 h1) (fun h1 : term68 = True => @lem1993081)). Qed.
Lemma lem1993084 : term68 = True.
Proof. exact (EQ_MP (@lem1993083) (@lem1993081)). Qed.
Lemma lem1993085 : term57 = True.
Proof. exact (TRANS (@lem1993080) (@lem1993084)). Qed.
Lemma lem1993086 : True = term57.
Proof. exact (SYM (@lem1993085)). Qed.
Lemma lem1993087 : term57.
Proof. exact (EQ_MP (@lem1993086) (@lem0)). Qed.
Lemma lem1993088 : term117.
Proof. exact (@lem1993077 (@lem1993087)). Qed.
Lemma lem1993090 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993091 : term74 = term75.
Proof. exact (@lem1993090 term61 term61). Qed.
Lemma lem1993092 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993093 : term77 = term61.
Proof. exact (EQ_MP (@lem1993092) (@lem940073)). Qed.
Lemma lem1993094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993095 : term75 = term58.
Proof. exact (MK_COMB (@lem1993094) (@lem1993093)). Qed.
Lemma lem1993096 : term74 = term58.
Proof. exact (TRANS (@lem1993091) (@lem1993095)). Qed.
Lemma lem1993098 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993099 : term120 = term121.
Proof. exact (@lem1993098 term61 term61). Qed.
Lemma lem1993100 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993101 : term77 = term61.
Proof. exact (EQ_MP (@lem1993100) (@lem940073)). Qed.
Lemma lem1993102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993103 : term75 = term58.
Proof. exact (MK_COMB (@lem1993102) (@lem1993101)). Qed.
Lemma lem1993104 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993105 : term121 = term106.
Proof. exact (MK_COMB (@lem1993104) (@lem1993103)). Qed.
Lemma lem1993106 : term120 = term106.
Proof. exact (TRANS (@lem1993099) (@lem1993105)). Qed.
Lemma lem1993107 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993108 : term122 = term110.
Proof. exact (MK_COMB (@lem1993107) (@lem1993106)). Qed.
Lemma lem1993109 : term123 = term112.
Proof. exact (MK_COMB (@lem1993108) (@lem1993096)). Qed.
Lemma lem1993111 (m : nat) : (term124 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1993112 : term112 = term24.
Proof. exact (@lem1993111 term61). Qed.
Lemma lem1993113 : term123 = term24.
Proof. exact (TRANS (@lem1993109) (@lem1993112)). Qed.
Lemma lem1993114 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993115 : term125 = term126.
Proof. exact (MK_COMB (@lem1993114) (@lem1993113)). Qed.
Lemma lem1993116 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1993117 : term127 = term79.
Proof. exact (MK_COMB (@lem1993115) (@lem1993116)). Qed.
Lemma lem1993119 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993120 : term79 = term24.
Proof. exact (@lem1993119 term61). Qed.
Lemma lem1993121 : term127 = term24.
Proof. exact (TRANS (@lem1993117) (@lem1993120)). Qed.
Lemma lem1993123 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993124 : term74 = term75.
Proof. exact (@lem1993123 term61 term61). Qed.
Lemma lem1993125 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993126 : term77 = term61.
Proof. exact (EQ_MP (@lem1993125) (@lem940073)). Qed.
Lemma lem1993127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993128 : term75 = term58.
Proof. exact (MK_COMB (@lem1993127) (@lem1993126)). Qed.
Lemma lem1993129 : term74 = term58.
Proof. exact (TRANS (@lem1993124) (@lem1993128)). Qed.
Lemma lem1993130 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1993131 : term128 = term79.
Proof. exact (MK_COMB (@lem1993130) (@lem1993129)). Qed.
Lemma lem1993133 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993134 : term79 = term24.
Proof. exact (@lem1993133 term61). Qed.
Lemma lem1993135 : term128 = term24.
Proof. exact (TRANS (@lem1993131) (@lem1993134)). Qed.
Lemma lem1993136 : term24 = term128.
Proof. exact (SYM (@lem1993135)). Qed.
Lemma lem1993137 : term127 = term128.
Proof. exact (TRANS (@lem1993121) (@lem1993136)). Qed.
Lemma lem1993138 : term113 = term62.
Proof. exact (@lem1993088 (@lem1993137)). Qed.
Lemma lem1993139 : term112 = term62.
Proof. exact (TRANS (@lem1993054) (@lem1993138)). Qed.
Lemma lem1993141 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1993142 : term62 = term24.
Proof. exact (@lem1993141 term24). Qed.
Lemma lem1993143 : term112 = term24.
Proof. exact (TRANS (@lem1993139) (@lem1993142)). Qed.
Lemma lem1993144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993145 : term130 = term126.
Proof. exact (MK_COMB (@lem1993144) (@lem1993143)). Qed.
Lemma lem1993146 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1993147 (z : real) : (term105 z) = (term131 z).
Proof. exact (MK_COMB (@lem1993145) (@lem1993146 z)). Qed.
Lemma lem1993148 (z : real) : (term104 z) = (term131 z).
Proof. exact (TRANS (@lem1993045 z) (@lem1993147 z)). Qed.
Lemma lem1993149 (z : real) : (term131 z) = term24.
Proof. exact (@lem1982719 z). Qed.
Lemma lem1993150 (z : real) : (term104 z) = term24.
Proof. exact (TRANS (@lem1993148 z) (@lem1993149 z)). Qed.
Lemma lem1993151 (y : real) : (term132 y) = (term132 y).
Proof. exact (eq_refl (term132 y)). Qed.
Lemma lem1993152 (z : real) (y : real) : (term103 y z) = (term133 y).
Proof. exact (MK_COMB (@lem1993151 y) (@lem1993150 z)). Qed.
Lemma lem1993153 (z : real) (y : real) : (term102 y z) = (term133 y).
Proof. exact (TRANS (@lem1993044 y z) (@lem1993152 z y)). Qed.
Lemma lem1993154 (y : real) : (term133 y) = (term21 y).
Proof. exact (@lem1982723 (term21 y)). Qed.
Lemma lem1993155 (z : real) (y : real) : (term102 y z) = (term21 y).
Proof. exact (TRANS (@lem1993153 z y) (@lem1993154 y)). Qed.
Lemma lem1993156 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1993157 (z : real) (x : real) (y : real) : (term101 x y z) = (term19 x y).
Proof. exact (MK_COMB (@lem1993156 x) (@lem1993155 z y)). Qed.
Lemma lem1993158 (z : real) (x : real) (y : real) : (term100 y x z) = (term19 x y).
Proof. exact (TRANS (@lem1993043 x y z) (@lem1993157 z x y)). Qed.
Lemma lem1993159 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1993160 (z : real) (x : real) (y : real) : (term134 y x z) = (term135 x y).
Proof. exact (MK_COMB (@lem1993159) (@lem1993158 z x y)). Qed.
Lemma lem1993161 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1993162 (z : real) (x : real) (y : real) : (term99 y x z) = (term136 x y).
Proof. exact (MK_COMB (@lem1993160 z x y) (@lem1993161)). Qed.
Lemma lem1993163 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term136 x y.
Proof. exact (EQ_MP (@lem1993162 z x y) (@lem1993042 y x z h1)). Qed.
Lemma lem1993165 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1993166 : term56 = term57.
Proof. exact (@lem1993165 term24 term58). Qed.
Lemma lem1993168 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993169 : term58 = term60.
Proof. exact (@lem1993168 term61). Qed.
Lemma lem1993171 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993172 : term24 = term62.
Proof. exact (@lem1993171 (NUMERAL 0)). Qed.
Lemma lem1993173 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1993174 : term63 = term64.
Proof. exact (MK_COMB (@lem1993173) (@lem1993172)). Qed.
Lemma lem1993175 : term57 = term65.
Proof. exact (MK_COMB (@lem1993174) (@lem1993169)). Qed.
Lemma lem1993176 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1993178 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993179 : term57 = term68.
Proof. exact (@lem1993178 (NUMERAL 0) term61). Qed.
Lemma lem1993180 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993181 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993182 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993181 h1) (fun h1 : term68 = True => @lem1993180)). Qed.
Lemma lem1993183 : term68 = True.
Proof. exact (EQ_MP (@lem1993182) (@lem1993180)). Qed.
Lemma lem1993184 : term57 = True.
Proof. exact (TRANS (@lem1993179) (@lem1993183)). Qed.
Lemma lem1993185 : True = term57.
Proof. exact (SYM (@lem1993184)). Qed.
Lemma lem1993186 : term57.
Proof. exact (EQ_MP (@lem1993185) (@lem0)). Qed.
Lemma lem1993187 : term70.
Proof. exact (@lem1993176 (@lem1993186)). Qed.
Lemma lem1993189 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993190 : term57 = term68.
Proof. exact (@lem1993189 (NUMERAL 0) term61). Qed.
Lemma lem1993191 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993192 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993193 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993192 h1) (fun h1 : term68 = True => @lem1993191)). Qed.
Lemma lem1993194 : term68 = True.
Proof. exact (EQ_MP (@lem1993193) (@lem1993191)). Qed.
Lemma lem1993195 : term57 = True.
Proof. exact (TRANS (@lem1993190) (@lem1993194)). Qed.
Lemma lem1993196 : True = term57.
Proof. exact (SYM (@lem1993195)). Qed.
Lemma lem1993197 : term57.
Proof. exact (EQ_MP (@lem1993196) (@lem0)). Qed.
Lemma lem1993198 : term65 = term71.
Proof. exact (@lem1993187 (@lem1993197)). Qed.
Lemma lem1993200 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993201 : term74 = term75.
Proof. exact (@lem1993200 term61 term61). Qed.
Lemma lem1993202 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993203 : term77 = term61.
Proof. exact (EQ_MP (@lem1993202) (@lem940073)). Qed.
Lemma lem1993204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993205 : term75 = term58.
Proof. exact (MK_COMB (@lem1993204) (@lem1993203)). Qed.
Lemma lem1993206 : term74 = term58.
Proof. exact (TRANS (@lem1993201) (@lem1993205)). Qed.
Lemma lem1993208 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993209 : term79 = term24.
Proof. exact (@lem1993208 term61). Qed.
Lemma lem1993210 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1993211 : term80 = term63.
Proof. exact (MK_COMB (@lem1993210) (@lem1993209)). Qed.
Lemma lem1993212 : term71 = term57.
Proof. exact (MK_COMB (@lem1993211) (@lem1993206)). Qed.
Lemma lem1993214 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993215 : term57 = term68.
Proof. exact (@lem1993214 (NUMERAL 0) term61). Qed.
Lemma lem1993216 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993217 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993218 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993217 h1) (fun h1 : term68 = True => @lem1993216)). Qed.
Lemma lem1993219 : term68 = True.
Proof. exact (EQ_MP (@lem1993218) (@lem1993216)). Qed.
Lemma lem1993220 : term57 = True.
Proof. exact (TRANS (@lem1993215) (@lem1993219)). Qed.
Lemma lem1993221 : term71 = True.
Proof. exact (TRANS (@lem1993212) (@lem1993220)). Qed.
Lemma lem1993222 : term65 = True.
Proof. exact (TRANS (@lem1993198) (@lem1993221)). Qed.
Lemma lem1993223 : term57 = True.
Proof. exact (TRANS (@lem1993175) (@lem1993222)). Qed.
Lemma lem1993224 : term56 = True.
Proof. exact (TRANS (@lem1993166) (@lem1993223)). Qed.
Lemma lem1993225 : True = term56.
Proof. exact (SYM (@lem1993224)). Qed.
Lemma lem1993226 : term56.
Proof. exact (EQ_MP (@lem1993225) (@lem0)). Qed.
Lemma lem1993227 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term137 x y.
Proof. exact (conj (@lem1993226) (@lem1993163 y x z h1)). Qed.
Lemma lem1993229 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1993230 (x : real) (y : real) : term138 x y.
Proof. exact (@lem1993229 term58 (term19 x y)). Qed.
Lemma lem1993231 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term139 x y.
Proof. exact (@lem1993230 x y (@lem1993227 y x z h1)). Qed.
Lemma lem1993232 (x : real) (y : real) : (term90 x y) = (term19 x y).
Proof. exact (@lem1982733 (term19 x y)). Qed.
Lemma lem1993233 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1993234 (x : real) (y : real) : (term140 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1993233) (@lem1993232 x y)). Qed.
Lemma lem1993235 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1993236 (x : real) (y : real) : (term139 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1993234 x y) (@lem1993235)). Qed.
Lemma lem1993237 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term136 x y.
Proof. exact (EQ_MP (@lem1993236 x y) (@lem1993231 y x z h1)). Qed.
Lemma lem1993238 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term141 x y.
Proof. exact (conj (@lem1993237 y x z h1) (@lem1992889 y x z h1)). Qed.
Lemma lem1993240 (x : real) (y : real) : term97 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1993241 (x : real) (y : real) : term142 x y.
Proof. exact (@lem1993240 (term19 x y) (term20 x y)). Qed.
Lemma lem1993242 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term143 x y.
Proof. exact (@lem1993241 x y (@lem1993238 y x z h1)). Qed.
Lemma lem1993243 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (@lem1982753 x (term21 x) (term21 y) y). Qed.
Lemma lem1993244 (x : real) : (term104 x) = (term105 x).
Proof. exact (@lem1982715 term106 x). Qed.
Lemma lem1993246 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993247 : term58 = term60.
Proof. exact (@lem1993246 term61). Qed.
Lemma lem1993249 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1993250 : term106 = term109.
Proof. exact (@lem1993249 term61). Qed.
Lemma lem1993251 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993252 : term110 = term111.
Proof. exact (MK_COMB (@lem1993251) (@lem1993250)). Qed.
Lemma lem1993253 : term112 = term113.
Proof. exact (MK_COMB (@lem1993252) (@lem1993247)). Qed.
Lemma lem1993254 : term114.
Proof. exact (@lem1981473 term106 term58 term58 term58 term24 term58). Qed.
Lemma lem1993256 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993257 : term57 = term68.
Proof. exact (@lem1993256 (NUMERAL 0) term61). Qed.
Lemma lem1993258 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993259 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993260 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993259 h1) (fun h1 : term68 = True => @lem1993258)). Qed.
Lemma lem1993261 : term68 = True.
Proof. exact (EQ_MP (@lem1993260) (@lem1993258)). Qed.
Lemma lem1993262 : term57 = True.
Proof. exact (TRANS (@lem1993257) (@lem1993261)). Qed.
Lemma lem1993263 : True = term57.
Proof. exact (SYM (@lem1993262)). Qed.
Lemma lem1993264 : term57.
Proof. exact (EQ_MP (@lem1993263) (@lem0)). Qed.
Lemma lem1993265 : term115.
Proof. exact (@lem1993254 (@lem1993264)). Qed.
Lemma lem1993267 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993268 : term57 = term68.
Proof. exact (@lem1993267 (NUMERAL 0) term61). Qed.
Lemma lem1993269 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993270 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993271 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993270 h1) (fun h1 : term68 = True => @lem1993269)). Qed.
Lemma lem1993272 : term68 = True.
Proof. exact (EQ_MP (@lem1993271) (@lem1993269)). Qed.
Lemma lem1993273 : term57 = True.
Proof. exact (TRANS (@lem1993268) (@lem1993272)). Qed.
Lemma lem1993274 : True = term57.
Proof. exact (SYM (@lem1993273)). Qed.
Lemma lem1993275 : term57.
Proof. exact (EQ_MP (@lem1993274) (@lem0)). Qed.
Lemma lem1993276 : term116.
Proof. exact (@lem1993265 (@lem1993275)). Qed.
Lemma lem1993278 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993279 : term57 = term68.
Proof. exact (@lem1993278 (NUMERAL 0) term61). Qed.
Lemma lem1993280 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993281 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993282 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993281 h1) (fun h1 : term68 = True => @lem1993280)). Qed.
Lemma lem1993283 : term68 = True.
Proof. exact (EQ_MP (@lem1993282) (@lem1993280)). Qed.
Lemma lem1993284 : term57 = True.
Proof. exact (TRANS (@lem1993279) (@lem1993283)). Qed.
Lemma lem1993285 : True = term57.
Proof. exact (SYM (@lem1993284)). Qed.
Lemma lem1993286 : term57.
Proof. exact (EQ_MP (@lem1993285) (@lem0)). Qed.
Lemma lem1993287 : term117.
Proof. exact (@lem1993276 (@lem1993286)). Qed.
Lemma lem1993289 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993290 : term74 = term75.
Proof. exact (@lem1993289 term61 term61). Qed.
Lemma lem1993291 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993292 : term77 = term61.
Proof. exact (EQ_MP (@lem1993291) (@lem940073)). Qed.
Lemma lem1993293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993294 : term75 = term58.
Proof. exact (MK_COMB (@lem1993293) (@lem1993292)). Qed.
Lemma lem1993295 : term74 = term58.
Proof. exact (TRANS (@lem1993290) (@lem1993294)). Qed.
Lemma lem1993297 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993298 : term120 = term121.
Proof. exact (@lem1993297 term61 term61). Qed.
Lemma lem1993299 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993300 : term77 = term61.
Proof. exact (EQ_MP (@lem1993299) (@lem940073)). Qed.
Lemma lem1993301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993302 : term75 = term58.
Proof. exact (MK_COMB (@lem1993301) (@lem1993300)). Qed.
Lemma lem1993303 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993304 : term121 = term106.
Proof. exact (MK_COMB (@lem1993303) (@lem1993302)). Qed.
Lemma lem1993305 : term120 = term106.
Proof. exact (TRANS (@lem1993298) (@lem1993304)). Qed.
Lemma lem1993306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993307 : term122 = term110.
Proof. exact (MK_COMB (@lem1993306) (@lem1993305)). Qed.
Lemma lem1993308 : term123 = term112.
Proof. exact (MK_COMB (@lem1993307) (@lem1993295)). Qed.
Lemma lem1993310 (m : nat) : (term124 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1993311 : term112 = term24.
Proof. exact (@lem1993310 term61). Qed.
Lemma lem1993312 : term123 = term24.
Proof. exact (TRANS (@lem1993308) (@lem1993311)). Qed.
Lemma lem1993313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993314 : term125 = term126.
Proof. exact (MK_COMB (@lem1993313) (@lem1993312)). Qed.
Lemma lem1993315 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1993316 : term127 = term79.
Proof. exact (MK_COMB (@lem1993314) (@lem1993315)). Qed.
Lemma lem1993318 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993319 : term79 = term24.
Proof. exact (@lem1993318 term61). Qed.
Lemma lem1993320 : term127 = term24.
Proof. exact (TRANS (@lem1993316) (@lem1993319)). Qed.
Lemma lem1993322 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993323 : term74 = term75.
Proof. exact (@lem1993322 term61 term61). Qed.
Lemma lem1993324 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993325 : term77 = term61.
Proof. exact (EQ_MP (@lem1993324) (@lem940073)). Qed.
Lemma lem1993326 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993327 : term75 = term58.
Proof. exact (MK_COMB (@lem1993326) (@lem1993325)). Qed.
Lemma lem1993328 : term74 = term58.
Proof. exact (TRANS (@lem1993323) (@lem1993327)). Qed.
Lemma lem1993329 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1993330 : term128 = term79.
Proof. exact (MK_COMB (@lem1993329) (@lem1993328)). Qed.
Lemma lem1993332 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993333 : term79 = term24.
Proof. exact (@lem1993332 term61). Qed.
Lemma lem1993334 : term128 = term24.
Proof. exact (TRANS (@lem1993330) (@lem1993333)). Qed.
Lemma lem1993335 : term24 = term128.
Proof. exact (SYM (@lem1993334)). Qed.
Lemma lem1993336 : term127 = term128.
Proof. exact (TRANS (@lem1993320) (@lem1993335)). Qed.
Lemma lem1993337 : term113 = term62.
Proof. exact (@lem1993287 (@lem1993336)). Qed.
Lemma lem1993338 : term112 = term62.
Proof. exact (TRANS (@lem1993253) (@lem1993337)). Qed.
Lemma lem1993340 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1993341 : term62 = term24.
Proof. exact (@lem1993340 term24). Qed.
Lemma lem1993342 : term112 = term24.
Proof. exact (TRANS (@lem1993338) (@lem1993341)). Qed.
Lemma lem1993343 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993344 : term130 = term126.
Proof. exact (MK_COMB (@lem1993343) (@lem1993342)). Qed.
Lemma lem1993345 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1993346 (x : real) : (term105 x) = (term131 x).
Proof. exact (MK_COMB (@lem1993344) (@lem1993345 x)). Qed.
Lemma lem1993347 (x : real) : (term104 x) = (term131 x).
Proof. exact (TRANS (@lem1993244 x) (@lem1993346 x)). Qed.
Lemma lem1993348 (x : real) : (term131 x) = term24.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1993349 (x : real) : (term104 x) = term24.
Proof. exact (TRANS (@lem1993347 x) (@lem1993348 x)). Qed.
Lemma lem1993350 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993351 (x : real) : (term146 x) = term147.
Proof. exact (MK_COMB (@lem1993350) (@lem1993349 x)). Qed.
Lemma lem1993352 (y : real) : (term148 y) = (term105 y).
Proof. exact (@lem1982713 term106 y). Qed.
Lemma lem1993354 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993355 : term58 = term60.
Proof. exact (@lem1993354 term61). Qed.
Lemma lem1993357 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1993358 : term106 = term109.
Proof. exact (@lem1993357 term61). Qed.
Lemma lem1993359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993360 : term110 = term111.
Proof. exact (MK_COMB (@lem1993359) (@lem1993358)). Qed.
Lemma lem1993361 : term112 = term113.
Proof. exact (MK_COMB (@lem1993360) (@lem1993355)). Qed.
Lemma lem1993362 : term114.
Proof. exact (@lem1981473 term106 term58 term58 term58 term24 term58). Qed.
Lemma lem1993364 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993365 : term57 = term68.
Proof. exact (@lem1993364 (NUMERAL 0) term61). Qed.
Lemma lem1993366 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993367 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993368 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993367 h1) (fun h1 : term68 = True => @lem1993366)). Qed.
Lemma lem1993369 : term68 = True.
Proof. exact (EQ_MP (@lem1993368) (@lem1993366)). Qed.
Lemma lem1993370 : term57 = True.
Proof. exact (TRANS (@lem1993365) (@lem1993369)). Qed.
Lemma lem1993371 : True = term57.
Proof. exact (SYM (@lem1993370)). Qed.
Lemma lem1993372 : term57.
Proof. exact (EQ_MP (@lem1993371) (@lem0)). Qed.
Lemma lem1993373 : term115.
Proof. exact (@lem1993362 (@lem1993372)). Qed.
Lemma lem1993375 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993376 : term57 = term68.
Proof. exact (@lem1993375 (NUMERAL 0) term61). Qed.
Lemma lem1993377 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993378 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993379 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993378 h1) (fun h1 : term68 = True => @lem1993377)). Qed.
Lemma lem1993380 : term68 = True.
Proof. exact (EQ_MP (@lem1993379) (@lem1993377)). Qed.
Lemma lem1993381 : term57 = True.
Proof. exact (TRANS (@lem1993376) (@lem1993380)). Qed.
Lemma lem1993382 : True = term57.
Proof. exact (SYM (@lem1993381)). Qed.
Lemma lem1993383 : term57.
Proof. exact (EQ_MP (@lem1993382) (@lem0)). Qed.
Lemma lem1993384 : term116.
Proof. exact (@lem1993373 (@lem1993383)). Qed.
Lemma lem1993386 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993387 : term57 = term68.
Proof. exact (@lem1993386 (NUMERAL 0) term61). Qed.
Lemma lem1993388 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993389 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993390 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993389 h1) (fun h1 : term68 = True => @lem1993388)). Qed.
Lemma lem1993391 : term68 = True.
Proof. exact (EQ_MP (@lem1993390) (@lem1993388)). Qed.
Lemma lem1993392 : term57 = True.
Proof. exact (TRANS (@lem1993387) (@lem1993391)). Qed.
Lemma lem1993393 : True = term57.
Proof. exact (SYM (@lem1993392)). Qed.
Lemma lem1993394 : term57.
Proof. exact (EQ_MP (@lem1993393) (@lem0)). Qed.
Lemma lem1993395 : term117.
Proof. exact (@lem1993384 (@lem1993394)). Qed.
Lemma lem1993397 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993398 : term74 = term75.
Proof. exact (@lem1993397 term61 term61). Qed.
Lemma lem1993399 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993400 : term77 = term61.
Proof. exact (EQ_MP (@lem1993399) (@lem940073)). Qed.
Lemma lem1993401 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993402 : term75 = term58.
Proof. exact (MK_COMB (@lem1993401) (@lem1993400)). Qed.
Lemma lem1993403 : term74 = term58.
Proof. exact (TRANS (@lem1993398) (@lem1993402)). Qed.
Lemma lem1993405 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993406 : term120 = term121.
Proof. exact (@lem1993405 term61 term61). Qed.
Lemma lem1993407 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993408 : term77 = term61.
Proof. exact (EQ_MP (@lem1993407) (@lem940073)). Qed.
Lemma lem1993409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993410 : term75 = term58.
Proof. exact (MK_COMB (@lem1993409) (@lem1993408)). Qed.
Lemma lem1993411 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993412 : term121 = term106.
Proof. exact (MK_COMB (@lem1993411) (@lem1993410)). Qed.
Lemma lem1993413 : term120 = term106.
Proof. exact (TRANS (@lem1993406) (@lem1993412)). Qed.
Lemma lem1993414 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993415 : term122 = term110.
Proof. exact (MK_COMB (@lem1993414) (@lem1993413)). Qed.
Lemma lem1993416 : term123 = term112.
Proof. exact (MK_COMB (@lem1993415) (@lem1993403)). Qed.
Lemma lem1993418 (m : nat) : (term124 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1993419 : term112 = term24.
Proof. exact (@lem1993418 term61). Qed.
Lemma lem1993420 : term123 = term24.
Proof. exact (TRANS (@lem1993416) (@lem1993419)). Qed.
Lemma lem1993421 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993422 : term125 = term126.
Proof. exact (MK_COMB (@lem1993421) (@lem1993420)). Qed.
Lemma lem1993423 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1993424 : term127 = term79.
Proof. exact (MK_COMB (@lem1993422) (@lem1993423)). Qed.
Lemma lem1993426 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993427 : term79 = term24.
Proof. exact (@lem1993426 term61). Qed.
Lemma lem1993428 : term127 = term24.
Proof. exact (TRANS (@lem1993424) (@lem1993427)). Qed.
Lemma lem1993430 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993431 : term74 = term75.
Proof. exact (@lem1993430 term61 term61). Qed.
Lemma lem1993432 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993433 : term77 = term61.
Proof. exact (EQ_MP (@lem1993432) (@lem940073)). Qed.
Lemma lem1993434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993435 : term75 = term58.
Proof. exact (MK_COMB (@lem1993434) (@lem1993433)). Qed.
Lemma lem1993436 : term74 = term58.
Proof. exact (TRANS (@lem1993431) (@lem1993435)). Qed.
Lemma lem1993437 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1993438 : term128 = term79.
Proof. exact (MK_COMB (@lem1993437) (@lem1993436)). Qed.
Lemma lem1993440 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993441 : term79 = term24.
Proof. exact (@lem1993440 term61). Qed.
Lemma lem1993442 : term128 = term24.
Proof. exact (TRANS (@lem1993438) (@lem1993441)). Qed.
Lemma lem1993443 : term24 = term128.
Proof. exact (SYM (@lem1993442)). Qed.
Lemma lem1993444 : term127 = term128.
Proof. exact (TRANS (@lem1993428) (@lem1993443)). Qed.
Lemma lem1993445 : term113 = term62.
Proof. exact (@lem1993395 (@lem1993444)). Qed.
Lemma lem1993446 : term112 = term62.
Proof. exact (TRANS (@lem1993361) (@lem1993445)). Qed.
Lemma lem1993448 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1993449 : term62 = term24.
Proof. exact (@lem1993448 term24). Qed.
Lemma lem1993450 : term112 = term24.
Proof. exact (TRANS (@lem1993446) (@lem1993449)). Qed.
Lemma lem1993451 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993452 : term130 = term126.
Proof. exact (MK_COMB (@lem1993451) (@lem1993450)). Qed.
Lemma lem1993453 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1993454 (y : real) : (term105 y) = (term131 y).
Proof. exact (MK_COMB (@lem1993452) (@lem1993453 y)). Qed.
Lemma lem1993455 (y : real) : (term148 y) = (term131 y).
Proof. exact (TRANS (@lem1993352 y) (@lem1993454 y)). Qed.
Lemma lem1993456 (y : real) : (term131 y) = term24.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1993457 (y : real) : (term148 y) = term24.
Proof. exact (TRANS (@lem1993455 y) (@lem1993456 y)). Qed.
Lemma lem1993458 (x : real) (y : real) : (term145 x y) = term149.
Proof. exact (MK_COMB (@lem1993351 x) (@lem1993457 y)). Qed.
Lemma lem1993459 (x : real) (y : real) : (term144 x y) = term149.
Proof. exact (TRANS (@lem1993243 x y) (@lem1993458 x y)). Qed.
Lemma lem1993460 : term149 = term24.
Proof. exact (@lem1982721 term24). Qed.
Lemma lem1993461 (x : real) (y : real) : (term144 x y) = term24.
Proof. exact (TRANS (@lem1993459 x y) (@lem1993460)). Qed.
Lemma lem1993462 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1993463 (x : real) (y : real) : (term150 x y) = term151.
Proof. exact (MK_COMB (@lem1993462) (@lem1993461 x y)). Qed.
Lemma lem1993464 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1993465 (x : real) (y : real) : (term143 x y) = term152.
Proof. exact (MK_COMB (@lem1993463 x y) (@lem1993464)). Qed.
Lemma lem1993466 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term152.
Proof. exact (EQ_MP (@lem1993465 x y) (@lem1993242 y x z h1)). Qed.
Lemma lem1993468 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1993469 : term152 = term153.
Proof. exact (@lem1993468 term24 term24). Qed.
Lemma lem1993471 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993472 : term24 = term62.
Proof. exact (@lem1993471 (NUMERAL 0)). Qed.
Lemma lem1993474 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993475 : term24 = term62.
Proof. exact (@lem1993474 (NUMERAL 0)). Qed.
Lemma lem1993476 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1993477 : term63 = term64.
Proof. exact (MK_COMB (@lem1993476) (@lem1993475)). Qed.
Lemma lem1993478 : term153 = term154.
Proof. exact (MK_COMB (@lem1993477) (@lem1993472)). Qed.
Lemma lem1993479 : term155.
Proof. exact (@lem1980255 term24 term58 term24 term58). Qed.
Lemma lem1993481 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993482 : term57 = term68.
Proof. exact (@lem1993481 (NUMERAL 0) term61). Qed.
Lemma lem1993483 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993484 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993485 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993484 h1) (fun h1 : term68 = True => @lem1993483)). Qed.
Lemma lem1993486 : term68 = True.
Proof. exact (EQ_MP (@lem1993485) (@lem1993483)). Qed.
Lemma lem1993487 : term57 = True.
Proof. exact (TRANS (@lem1993482) (@lem1993486)). Qed.
Lemma lem1993488 : True = term57.
Proof. exact (SYM (@lem1993487)). Qed.
Lemma lem1993489 : term57.
Proof. exact (EQ_MP (@lem1993488) (@lem0)). Qed.
Lemma lem1993490 : term156.
Proof. exact (@lem1993479 (@lem1993489)). Qed.
Lemma lem1993492 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993493 : term57 = term68.
Proof. exact (@lem1993492 (NUMERAL 0) term61). Qed.
Lemma lem1993494 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993495 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993496 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993495 h1) (fun h1 : term68 = True => @lem1993494)). Qed.
Lemma lem1993497 : term68 = True.
Proof. exact (EQ_MP (@lem1993496) (@lem1993494)). Qed.
Lemma lem1993498 : term57 = True.
Proof. exact (TRANS (@lem1993493) (@lem1993497)). Qed.
Lemma lem1993499 : True = term57.
Proof. exact (SYM (@lem1993498)). Qed.
Lemma lem1993500 : term57.
Proof. exact (EQ_MP (@lem1993499) (@lem0)). Qed.
Lemma lem1993501 : term154 = term157.
Proof. exact (@lem1993490 (@lem1993500)). Qed.
Lemma lem1993503 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993504 : term79 = term24.
Proof. exact (@lem1993503 term61). Qed.
Lemma lem1993506 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1993507 : term79 = term24.
Proof. exact (@lem1993506 term61). Qed.
Lemma lem1993508 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1993509 : term80 = term63.
Proof. exact (MK_COMB (@lem1993508) (@lem1993507)). Qed.
Lemma lem1993510 : term157 = term153.
Proof. exact (MK_COMB (@lem1993509) (@lem1993504)). Qed.
Lemma lem1993512 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993513 : term153 = term158.
Proof. exact (@lem1993512 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1993514 : term158 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1993515 : term153 = False.
Proof. exact (TRANS (@lem1993513) (@lem1993514)). Qed.
Lemma lem1993516 : term157 = False.
Proof. exact (TRANS (@lem1993510) (@lem1993515)). Qed.
Lemma lem1993517 : term154 = False.
Proof. exact (TRANS (@lem1993501) (@lem1993516)). Qed.
Lemma lem1993518 : term153 = False.
Proof. exact (TRANS (@lem1993478) (@lem1993517)). Qed.
Lemma lem1993519 : term152 = False.
Proof. exact (TRANS (@lem1993469) (@lem1993518)). Qed.
Lemma lem1993520 (y : real) (x : real) (z : real) (h1 : term52 y x z) : False.
Proof. exact (EQ_MP (@lem1993519) (@lem1993466 y x z h1)). Qed.
Lemma lem1993522 (y : real) (x : real) (z : real) (h1 : term52 y x z) : term52 y x z.
Proof. exact (h1). Qed.
Lemma lem1993523 (y : real) (x : real) (z : real) (h1 : term52 y x z) : (term52 y x z) = False.
Proof. exact (prop_ext (fun h2 : term52 y x z => @lem1993520 y x z h1) (fun h2 : False => @lem1993522 y x z h1)). Qed.
Lemma lem1993524 (y : real) (x : real) (z : real) (h1 : term52 y x z) : False.
Proof. exact (EQ_MP (@lem1993523 y x z h1) (@lem1993522 y x z h1)). Qed.
Lemma lem1993525 (y : real) (x : real) (h1 : term55 y x) : term55 y x.
Proof. exact (h1). Qed.
Lemma lem1993526 (y : real) (x : real) (h1 : term55 y x) : False.
Proof. exact (ex_elim (@lem1993525 y x h1) (fun z : real => fun h0 : term54 y x z => @lem1993524 y x z h0)). Qed.
Lemma lem1993527 (y : real) (x : real) (h1 : term16 y x) : term16 y x.
Proof. exact (h1). Qed.
Lemma lem1993528 (y : real) (x : real) (h1 : term16 y x) : term55 y x.
Proof. exact (EQ_MP (@lem1992807 y x) (@lem1993527 y x h1)). Qed.
Lemma lem1993529 (y : real) (x : real) (h1 : term16 y x) : (term55 y x) = False.
Proof. exact (prop_ext (fun h2 : term55 y x => @lem1993526 y x h2) (fun h2 : False => @lem1993528 y x h1)). Qed.
Lemma lem1993530 (y : real) (x : real) (h1 : term16 y x) : False.
Proof. exact (EQ_MP (@lem1993529 y x h1) (@lem1993528 y x h1)). Qed.
Lemma lem1993531 (y : real) (x : real) : term159 y x.
Proof. exact (fun h0 : term16 y x => @lem1993530 y x h0). Qed.
Lemma lem1993532 (y : real) (x : real) : term160 y x.
Proof. exact (@lem1386578 (term161 y x)). Qed.
Lemma lem1993535 (y : real) (x : real) : term161 y x.
Proof. exact (@lem1993532 y x (@lem1993531 y x)). Qed.
Lemma lem1993536 (y : real) (x : real) (h1 : term17 y x) : term17 y x.
Proof. exact (h1). Qed.
Lemma lem1993537 (y : real) (x : real) (h1 : term17 y x) : term162 x y.
Proof. exact (@lem1993536 y x h1 (term163 x y)). Qed.
Lemma lem1993538 (x : real) (y : real) : (term162 x y) = (term164 x y).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem1993539 (y : real) (x : real) (h1 : term17 y x) : term164 x y.
Proof. exact (EQ_MP (@lem1993538 x y) (@lem1993537 y x h1)). Qed.
Lemma lem1993554 (x : real) (y : real) : (term164 x y) = (term165 x y).
Proof. exact (@lem17265 (term166 x y) (term167 x y)). Qed.
Lemma lem1993555 (x : real) (y : real) : (term168 x y) = (term168 x y).
Proof. exact (eq_refl (term168 x y)). Qed.
Lemma lem1993556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1993557 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem1993556) (@lem1993554 x y)). Qed.
Lemma lem1993558 (x : real) (y : real) : (term171 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem1993557 x y) (@lem1993555 x y)). Qed.
Lemma lem1993559 (x : real) (y : real) : (term173 x y) = (term171 x y).
Proof. exact (@lem17362 (term164 x y) (real_le x y)). Qed.
Lemma lem1993575 (x : real) (y : real) : (term173 x y) = (term172 x y).
Proof. exact (TRANS (@lem1993559 x y) (@lem1993558 x y)). Qed.
Lemma lem1993576 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1988295 y (term163 x y)). Qed.
Lemma lem1993578 (x : real) (y : real) : (real_div x y) = (term176 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem1993579 (x : real) (y : real) : (term177 x y) = (term178 x y).
Proof. exact (@lem1993578 (real_sub x y) term179). Qed.
Lemma lem1993584 (n : nat) : (term180 n) = (term181 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem1993586 : term182 = term183.
Proof. exact (@lem1993584 term184). Qed.
Lemma lem1993599 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1993600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993601 (x : real) (y : real) : (term185 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1993600) (@lem1993599 x y)). Qed.
Lemma lem1993602 (x : real) (y : real) : (term178 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1993601 x y) (@lem1993586)). Qed.
Lemma lem1993603 (x : real) (y : real) : (term187 x y) = (term188 x y).
Proof. exact (@lem1982725 term183 (term19 x y)). Qed.
Lemma lem1993604 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1982781 x term183 (term21 y)). Qed.
Lemma lem1993605 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1982749 term183 term106 y). Qed.
Lemma lem1993607 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1993608 : term106 = term109.
Proof. exact (@lem1993607 term61). Qed.
Lemma lem1993611 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1993612 : term193 = term194.
Proof. exact (MK_COMB (@lem1993611) (@lem1993608)). Qed.
Lemma lem1993613 : term194 = term195.
Proof. exact (@lem1981613 term58 term106 term179 term58). Qed.
Lemma lem1993615 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993616 : term196 = term197.
Proof. exact (@lem1993615 term184 term61). Qed.
Lemma lem1993617 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1993618 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1993619 : term200 = term184.
Proof. exact (EQ_MP (@lem1993618) (@lem1993617)). Qed.
Lemma lem1993620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993621 : term197 = term179.
Proof. exact (MK_COMB (@lem1993620) (@lem1993619)). Qed.
Lemma lem1993622 : term196 = term179.
Proof. exact (TRANS (@lem1993616) (@lem1993621)). Qed.
Lemma lem1993624 (m : nat) (n : nat) : (term201 m n) = (term119 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1993625 : term202 = term121.
Proof. exact (@lem1993624 term61 term61). Qed.
Lemma lem1993626 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993627 : term77 = term61.
Proof. exact (EQ_MP (@lem1993626) (@lem940073)). Qed.
Lemma lem1993628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993629 : term75 = term58.
Proof. exact (MK_COMB (@lem1993628) (@lem1993627)). Qed.
Lemma lem1993630 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993631 : term121 = term106.
Proof. exact (MK_COMB (@lem1993630) (@lem1993629)). Qed.
Lemma lem1993632 : term202 = term106.
Proof. exact (TRANS (@lem1993625) (@lem1993631)). Qed.
Lemma lem1993633 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1993634 : term203 = term204.
Proof. exact (MK_COMB (@lem1993633) (@lem1993632)). Qed.
Lemma lem1993635 : term195 = term205.
Proof. exact (MK_COMB (@lem1993634) (@lem1993622)). Qed.
Lemma lem1993636 : term194 = term205.
Proof. exact (TRANS (@lem1993613) (@lem1993635)). Qed.
Lemma lem1993639 : term193 = term205.
Proof. exact (TRANS (@lem1993612) (@lem1993636)). Qed.
Lemma lem1993640 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993641 : term206 = term207.
Proof. exact (MK_COMB (@lem1993640) (@lem1993639)). Qed.
Lemma lem1993642 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1993643 (y : real) : (term191 y) = (term208 y).
Proof. exact (MK_COMB (@lem1993641) (@lem1993642 y)). Qed.
Lemma lem1993644 (y : real) : (term190 y) = (term208 y).
Proof. exact (TRANS (@lem1993605 y) (@lem1993643 y)). Qed.
Lemma lem1993647 (x : real) : (term209 x) = (term209 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1993648 (x : real) (y : real) : (term189 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1993647 x) (@lem1993644 y)). Qed.
Lemma lem1993649 (x : real) (y : real) : (term188 x y) = (term210 x y).
Proof. exact (TRANS (@lem1993604 x y) (@lem1993648 x y)). Qed.
Lemma lem1993650 (x : real) (y : real) : (term187 x y) = (term210 x y).
Proof. exact (TRANS (@lem1993603 x y) (@lem1993649 x y)). Qed.
Lemma lem1993651 (x : real) (y : real) : (term178 x y) = (term210 x y).
Proof. exact (TRANS (@lem1993602 x y) (@lem1993650 x y)). Qed.
Lemma lem1993652 (x : real) (y : real) : (term177 x y) = (term210 x y).
Proof. exact (TRANS (@lem1993579 x y) (@lem1993651 x y)). Qed.
Lemma lem1993655 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1993656 (x : real) (y : real) : (term163 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1993655 y) (@lem1993652 x y)). Qed.
Lemma lem1993657 (x : real) (y : real) : (term211 x y) = (term212 x y).
Proof. exact (@lem1982757 (term213 x) y (term208 y)). Qed.
Lemma lem1993658 (y : real) : (term214 y) = (term215 y).
Proof. exact (@lem1982715 term205 y). Qed.
Lemma lem1993660 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993661 : term58 = term60.
Proof. exact (@lem1993660 term61). Qed.
Lemma lem1993664 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1993665 : term217 = term218.
Proof. exact (MK_COMB (@lem1993664) (@lem1993661)). Qed.
Lemma lem1993666 : term219.
Proof. exact (@lem1981473 term106 term179 term58 term58 term58 term179). Qed.
Lemma lem1993668 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993669 : term220 = term221.
Proof. exact (@lem1993668 (NUMERAL 0) term184). Qed.
Lemma lem1993670 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1993671 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1993672 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1993671 h1) (fun h1 : term221 = True => @lem1993670)). Qed.
Lemma lem1993673 : term221 = True.
Proof. exact (EQ_MP (@lem1993672) (@lem1993670)). Qed.
Lemma lem1993674 : term220 = True.
Proof. exact (TRANS (@lem1993669) (@lem1993673)). Qed.
Lemma lem1993675 : True = term220.
Proof. exact (SYM (@lem1993674)). Qed.
Lemma lem1993676 : term220.
Proof. exact (EQ_MP (@lem1993675) (@lem0)). Qed.
Lemma lem1993677 : term223.
Proof. exact (@lem1993666 (@lem1993676)). Qed.
Lemma lem1993679 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993680 : term57 = term68.
Proof. exact (@lem1993679 (NUMERAL 0) term61). Qed.
Lemma lem1993681 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993682 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993683 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993682 h1) (fun h1 : term68 = True => @lem1993681)). Qed.
Lemma lem1993684 : term68 = True.
Proof. exact (EQ_MP (@lem1993683) (@lem1993681)). Qed.
Lemma lem1993685 : term57 = True.
Proof. exact (TRANS (@lem1993680) (@lem1993684)). Qed.
Lemma lem1993686 : True = term57.
Proof. exact (SYM (@lem1993685)). Qed.
Lemma lem1993687 : term57.
Proof. exact (EQ_MP (@lem1993686) (@lem0)). Qed.
Lemma lem1993688 : term224.
Proof. exact (@lem1993677 (@lem1993687)). Qed.
Lemma lem1993690 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993691 : term220 = term221.
Proof. exact (@lem1993690 (NUMERAL 0) term184). Qed.
Lemma lem1993692 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1993693 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1993694 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1993693 h1) (fun h1 : term221 = True => @lem1993692)). Qed.
Lemma lem1993695 : term221 = True.
Proof. exact (EQ_MP (@lem1993694) (@lem1993692)). Qed.
Lemma lem1993696 : term220 = True.
Proof. exact (TRANS (@lem1993691) (@lem1993695)). Qed.
Lemma lem1993697 : True = term220.
Proof. exact (SYM (@lem1993696)). Qed.
Lemma lem1993698 : term220.
Proof. exact (EQ_MP (@lem1993697) (@lem0)). Qed.
Lemma lem1993699 : term225.
Proof. exact (@lem1993688 (@lem1993698)). Qed.
Lemma lem1993701 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993702 : term226 = term227.
Proof. exact (@lem1993701 term61 term184). Qed.
Lemma lem1993703 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993704 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993705 : term229 = term184.
Proof. exact (EQ_MP (@lem1993704) (@lem1993703)). Qed.
Lemma lem1993706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993707 : term227 = term179.
Proof. exact (MK_COMB (@lem1993706) (@lem1993705)). Qed.
Lemma lem1993708 : term226 = term179.
Proof. exact (TRANS (@lem1993702) (@lem1993707)). Qed.
Lemma lem1993710 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993711 : term120 = term121.
Proof. exact (@lem1993710 term61 term61). Qed.
Lemma lem1993712 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993713 : term77 = term61.
Proof. exact (EQ_MP (@lem1993712) (@lem940073)). Qed.
Lemma lem1993714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993715 : term75 = term58.
Proof. exact (MK_COMB (@lem1993714) (@lem1993713)). Qed.
Lemma lem1993716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993717 : term121 = term106.
Proof. exact (MK_COMB (@lem1993716) (@lem1993715)). Qed.
Lemma lem1993718 : term120 = term106.
Proof. exact (TRANS (@lem1993711) (@lem1993717)). Qed.
Lemma lem1993719 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993720 : term122 = term110.
Proof. exact (MK_COMB (@lem1993719) (@lem1993718)). Qed.
Lemma lem1993721 : term230 = term231.
Proof. exact (MK_COMB (@lem1993720) (@lem1993708)). Qed.
Lemma lem1993724 : term232 = term58.
Proof. exact (@lem1367765 term61 term61). Qed.
Lemma lem1993725 : term233 = term199.
Proof. exact (@lem706885). Qed.
Lemma lem1993726 : (term233 = term199) = (term234 = term184).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term199). Qed.
Lemma lem1993727 : term234 = term184.
Proof. exact (EQ_MP (@lem1993726) (@lem1993725)). Qed.
Lemma lem1993728 : term184 = term234.
Proof. exact (SYM (@lem1993727)). Qed.
Lemma lem1993729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993730 : term179 = term235.
Proof. exact (MK_COMB (@lem1993729) (@lem1993728)). Qed.
Lemma lem1993731 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem1993732 : term231 = term232.
Proof. exact (MK_COMB (@lem1993731) (@lem1993730)). Qed.
Lemma lem1993733 : term231 = term58.
Proof. exact (TRANS (@lem1993732) (@lem1993724)). Qed.
Lemma lem1993734 : term230 = term58.
Proof. exact (TRANS (@lem1993721) (@lem1993733)). Qed.
Lemma lem1993735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993736 : term236 = term237.
Proof. exact (MK_COMB (@lem1993735) (@lem1993734)). Qed.
Lemma lem1993737 : term179 = term179.
Proof. exact (eq_refl term179). Qed.
Lemma lem1993738 : term238 = term226.
Proof. exact (MK_COMB (@lem1993736) (@lem1993737)). Qed.
Lemma lem1993740 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993741 : term226 = term227.
Proof. exact (@lem1993740 term61 term184). Qed.
Lemma lem1993742 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993743 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993744 : term229 = term184.
Proof. exact (EQ_MP (@lem1993743) (@lem1993742)). Qed.
Lemma lem1993745 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993746 : term227 = term179.
Proof. exact (MK_COMB (@lem1993745) (@lem1993744)). Qed.
Lemma lem1993747 : term226 = term179.
Proof. exact (TRANS (@lem1993741) (@lem1993746)). Qed.
Lemma lem1993748 : term238 = term179.
Proof. exact (TRANS (@lem1993738) (@lem1993747)). Qed.
Lemma lem1993750 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993751 : term196 = term197.
Proof. exact (@lem1993750 term184 term61). Qed.
Lemma lem1993752 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1993753 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1993754 : term200 = term184.
Proof. exact (EQ_MP (@lem1993753) (@lem1993752)). Qed.
Lemma lem1993755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993756 : term197 = term179.
Proof. exact (MK_COMB (@lem1993755) (@lem1993754)). Qed.
Lemma lem1993757 : term196 = term179.
Proof. exact (TRANS (@lem1993751) (@lem1993756)). Qed.
Lemma lem1993758 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem1993759 : term239 = term226.
Proof. exact (MK_COMB (@lem1993758) (@lem1993757)). Qed.
Lemma lem1993761 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993762 : term226 = term227.
Proof. exact (@lem1993761 term61 term184). Qed.
Lemma lem1993763 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993764 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993765 : term229 = term184.
Proof. exact (EQ_MP (@lem1993764) (@lem1993763)). Qed.
Lemma lem1993766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993767 : term227 = term179.
Proof. exact (MK_COMB (@lem1993766) (@lem1993765)). Qed.
Lemma lem1993768 : term226 = term179.
Proof. exact (TRANS (@lem1993762) (@lem1993767)). Qed.
Lemma lem1993769 : term239 = term179.
Proof. exact (TRANS (@lem1993759) (@lem1993768)). Qed.
Lemma lem1993770 : term179 = term239.
Proof. exact (SYM (@lem1993769)). Qed.
Lemma lem1993771 : term238 = term239.
Proof. exact (TRANS (@lem1993748) (@lem1993770)). Qed.
Lemma lem1993772 : term218 = term183.
Proof. exact (@lem1993699 (@lem1993771)). Qed.
Lemma lem1993775 : term217 = term183.
Proof. exact (TRANS (@lem1993665) (@lem1993772)). Qed.
Lemma lem1993776 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993777 : term240 = term192.
Proof. exact (MK_COMB (@lem1993776) (@lem1993775)). Qed.
Lemma lem1993778 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1993779 (y : real) : (term215 y) = (term213 y).
Proof. exact (MK_COMB (@lem1993777) (@lem1993778 y)). Qed.
Lemma lem1993780 (y : real) : (term214 y) = (term213 y).
Proof. exact (TRANS (@lem1993658 y) (@lem1993779 y)). Qed.
Lemma lem1993781 (x : real) : (term209 x) = (term209 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1993782 (x : real) (y : real) : (term212 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1993781 x) (@lem1993780 y)). Qed.
Lemma lem1993783 (x : real) (y : real) : (term211 x y) = (term241 x y).
Proof. exact (TRANS (@lem1993657 x y) (@lem1993782 x y)). Qed.
Lemma lem1993784 (x : real) (y : real) : (term163 x y) = (term241 x y).
Proof. exact (TRANS (@lem1993656 x y) (@lem1993783 x y)). Qed.
Lemma lem1993787 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1993788 (x : real) (y : real) : (term242 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1993787 y) (@lem1993784 x y)). Qed.
Lemma lem1993789 (x : real) (y : real) : (term243 x y) = (term244 x y).
Proof. exact (@lem1982792 y (term241 x y)). Qed.
Lemma lem1993790 (x : real) (y : real) : (term245 x y) = (term246 x y).
Proof. exact (@lem1982781 (term213 x) term106 (term213 y)). Qed.
Lemma lem1993791 (y : real) : (term247 y) = (term248 y).
Proof. exact (@lem1982749 term106 term183 y). Qed.
Lemma lem1993792 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1993794 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1993795 : term106 = term109.
Proof. exact (@lem1993794 term61). Qed.
Lemma lem1993796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993797 : term249 = term250.
Proof. exact (MK_COMB (@lem1993796) (@lem1993795)). Qed.
Lemma lem1993798 : term251 = term252.
Proof. exact (MK_COMB (@lem1993797) (@lem1993792)). Qed.
Lemma lem1993799 : term252 = term253.
Proof. exact (@lem1981613 term106 term58 term58 term179). Qed.
Lemma lem1993801 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993802 : term226 = term227.
Proof. exact (@lem1993801 term61 term184). Qed.
Lemma lem1993803 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993804 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993805 : term229 = term184.
Proof. exact (EQ_MP (@lem1993804) (@lem1993803)). Qed.
Lemma lem1993806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993807 : term227 = term179.
Proof. exact (MK_COMB (@lem1993806) (@lem1993805)). Qed.
Lemma lem1993808 : term226 = term179.
Proof. exact (TRANS (@lem1993802) (@lem1993807)). Qed.
Lemma lem1993810 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993811 : term120 = term121.
Proof. exact (@lem1993810 term61 term61). Qed.
Lemma lem1993812 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993813 : term77 = term61.
Proof. exact (EQ_MP (@lem1993812) (@lem940073)). Qed.
Lemma lem1993814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993815 : term75 = term58.
Proof. exact (MK_COMB (@lem1993814) (@lem1993813)). Qed.
Lemma lem1993816 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993817 : term121 = term106.
Proof. exact (MK_COMB (@lem1993816) (@lem1993815)). Qed.
Lemma lem1993818 : term120 = term106.
Proof. exact (TRANS (@lem1993811) (@lem1993817)). Qed.
Lemma lem1993819 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1993820 : term254 = term204.
Proof. exact (MK_COMB (@lem1993819) (@lem1993818)). Qed.
Lemma lem1993821 : term253 = term205.
Proof. exact (MK_COMB (@lem1993820) (@lem1993808)). Qed.
Lemma lem1993822 : term252 = term205.
Proof. exact (TRANS (@lem1993799) (@lem1993821)). Qed.
Lemma lem1993825 : term251 = term205.
Proof. exact (TRANS (@lem1993798) (@lem1993822)). Qed.
Lemma lem1993826 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993827 : term255 = term207.
Proof. exact (MK_COMB (@lem1993826) (@lem1993825)). Qed.
Lemma lem1993828 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1993829 (y : real) : (term248 y) = (term208 y).
Proof. exact (MK_COMB (@lem1993827) (@lem1993828 y)). Qed.
Lemma lem1993830 (y : real) : (term247 y) = (term208 y).
Proof. exact (TRANS (@lem1993791 y) (@lem1993829 y)). Qed.
Lemma lem1993831 (x : real) : (term247 x) = (term248 x).
Proof. exact (@lem1982749 term106 term183 x). Qed.
Lemma lem1993832 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1993834 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1993835 : term106 = term109.
Proof. exact (@lem1993834 term61). Qed.
Lemma lem1993836 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993837 : term249 = term250.
Proof. exact (MK_COMB (@lem1993836) (@lem1993835)). Qed.
Lemma lem1993838 : term251 = term252.
Proof. exact (MK_COMB (@lem1993837) (@lem1993832)). Qed.
Lemma lem1993839 : term252 = term253.
Proof. exact (@lem1981613 term106 term58 term58 term179). Qed.
Lemma lem1993841 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993842 : term226 = term227.
Proof. exact (@lem1993841 term61 term184). Qed.
Lemma lem1993843 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993844 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993845 : term229 = term184.
Proof. exact (EQ_MP (@lem1993844) (@lem1993843)). Qed.
Lemma lem1993846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993847 : term227 = term179.
Proof. exact (MK_COMB (@lem1993846) (@lem1993845)). Qed.
Lemma lem1993848 : term226 = term179.
Proof. exact (TRANS (@lem1993842) (@lem1993847)). Qed.
Lemma lem1993850 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993851 : term120 = term121.
Proof. exact (@lem1993850 term61 term61). Qed.
Lemma lem1993852 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993853 : term77 = term61.
Proof. exact (EQ_MP (@lem1993852) (@lem940073)). Qed.
Lemma lem1993854 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993855 : term75 = term58.
Proof. exact (MK_COMB (@lem1993854) (@lem1993853)). Qed.
Lemma lem1993856 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993857 : term121 = term106.
Proof. exact (MK_COMB (@lem1993856) (@lem1993855)). Qed.
Lemma lem1993858 : term120 = term106.
Proof. exact (TRANS (@lem1993851) (@lem1993857)). Qed.
Lemma lem1993859 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1993860 : term254 = term204.
Proof. exact (MK_COMB (@lem1993859) (@lem1993858)). Qed.
Lemma lem1993861 : term253 = term205.
Proof. exact (MK_COMB (@lem1993860) (@lem1993848)). Qed.
Lemma lem1993862 : term252 = term205.
Proof. exact (TRANS (@lem1993839) (@lem1993861)). Qed.
Lemma lem1993865 : term251 = term205.
Proof. exact (TRANS (@lem1993838) (@lem1993862)). Qed.
Lemma lem1993866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993867 : term255 = term207.
Proof. exact (MK_COMB (@lem1993866) (@lem1993865)). Qed.
Lemma lem1993868 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1993869 (x : real) : (term248 x) = (term208 x).
Proof. exact (MK_COMB (@lem1993867) (@lem1993868 x)). Qed.
Lemma lem1993870 (x : real) : (term247 x) = (term208 x).
Proof. exact (TRANS (@lem1993831 x) (@lem1993869 x)). Qed.
Lemma lem1993871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993872 (x : real) : (term256 x) = (term257 x).
Proof. exact (MK_COMB (@lem1993871) (@lem1993870 x)). Qed.
Lemma lem1993873 (x : real) (y : real) : (term246 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1993872 x) (@lem1993830 y)). Qed.
Lemma lem1993874 (x : real) (y : real) : (term245 x y) = (term258 x y).
Proof. exact (TRANS (@lem1993790 x y) (@lem1993873 x y)). Qed.
Lemma lem1993875 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1993876 (x : real) (y : real) : (term244 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1993875 y) (@lem1993874 x y)). Qed.
Lemma lem1993877 (x : real) (y : real) : (term259 x y) = (term260 x y).
Proof. exact (@lem1982757 (term208 x) y (term208 y)). Qed.
Lemma lem1993878 (y : real) : (term214 y) = (term215 y).
Proof. exact (@lem1982715 term205 y). Qed.
Lemma lem1993880 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1993881 : term58 = term60.
Proof. exact (@lem1993880 term61). Qed.
Lemma lem1993884 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1993885 : term217 = term218.
Proof. exact (MK_COMB (@lem1993884) (@lem1993881)). Qed.
Lemma lem1993886 : term219.
Proof. exact (@lem1981473 term106 term179 term58 term58 term58 term179). Qed.
Lemma lem1993888 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993889 : term220 = term221.
Proof. exact (@lem1993888 (NUMERAL 0) term184). Qed.
Lemma lem1993890 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1993891 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1993892 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1993891 h1) (fun h1 : term221 = True => @lem1993890)). Qed.
Lemma lem1993893 : term221 = True.
Proof. exact (EQ_MP (@lem1993892) (@lem1993890)). Qed.
Lemma lem1993894 : term220 = True.
Proof. exact (TRANS (@lem1993889) (@lem1993893)). Qed.
Lemma lem1993895 : True = term220.
Proof. exact (SYM (@lem1993894)). Qed.
Lemma lem1993896 : term220.
Proof. exact (EQ_MP (@lem1993895) (@lem0)). Qed.
Lemma lem1993897 : term223.
Proof. exact (@lem1993886 (@lem1993896)). Qed.
Lemma lem1993899 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993900 : term57 = term68.
Proof. exact (@lem1993899 (NUMERAL 0) term61). Qed.
Lemma lem1993901 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1993902 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1993903 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1993902 h1) (fun h1 : term68 = True => @lem1993901)). Qed.
Lemma lem1993904 : term68 = True.
Proof. exact (EQ_MP (@lem1993903) (@lem1993901)). Qed.
Lemma lem1993905 : term57 = True.
Proof. exact (TRANS (@lem1993900) (@lem1993904)). Qed.
Lemma lem1993906 : True = term57.
Proof. exact (SYM (@lem1993905)). Qed.
Lemma lem1993907 : term57.
Proof. exact (EQ_MP (@lem1993906) (@lem0)). Qed.
Lemma lem1993908 : term224.
Proof. exact (@lem1993897 (@lem1993907)). Qed.
Lemma lem1993910 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1993911 : term220 = term221.
Proof. exact (@lem1993910 (NUMERAL 0) term184). Qed.
Lemma lem1993912 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1993913 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1993914 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1993913 h1) (fun h1 : term221 = True => @lem1993912)). Qed.
Lemma lem1993915 : term221 = True.
Proof. exact (EQ_MP (@lem1993914) (@lem1993912)). Qed.
Lemma lem1993916 : term220 = True.
Proof. exact (TRANS (@lem1993911) (@lem1993915)). Qed.
Lemma lem1993917 : True = term220.
Proof. exact (SYM (@lem1993916)). Qed.
Lemma lem1993918 : term220.
Proof. exact (EQ_MP (@lem1993917) (@lem0)). Qed.
Lemma lem1993919 : term225.
Proof. exact (@lem1993908 (@lem1993918)). Qed.
Lemma lem1993921 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993922 : term226 = term227.
Proof. exact (@lem1993921 term61 term184). Qed.
Lemma lem1993923 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993924 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993925 : term229 = term184.
Proof. exact (EQ_MP (@lem1993924) (@lem1993923)). Qed.
Lemma lem1993926 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993927 : term227 = term179.
Proof. exact (MK_COMB (@lem1993926) (@lem1993925)). Qed.
Lemma lem1993928 : term226 = term179.
Proof. exact (TRANS (@lem1993922) (@lem1993927)). Qed.
Lemma lem1993930 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1993931 : term120 = term121.
Proof. exact (@lem1993930 term61 term61). Qed.
Lemma lem1993932 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1993933 : term77 = term61.
Proof. exact (EQ_MP (@lem1993932) (@lem940073)). Qed.
Lemma lem1993934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993935 : term75 = term58.
Proof. exact (MK_COMB (@lem1993934) (@lem1993933)). Qed.
Lemma lem1993936 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1993937 : term121 = term106.
Proof. exact (MK_COMB (@lem1993936) (@lem1993935)). Qed.
Lemma lem1993938 : term120 = term106.
Proof. exact (TRANS (@lem1993931) (@lem1993937)). Qed.
Lemma lem1993939 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1993940 : term122 = term110.
Proof. exact (MK_COMB (@lem1993939) (@lem1993938)). Qed.
Lemma lem1993941 : term230 = term231.
Proof. exact (MK_COMB (@lem1993940) (@lem1993928)). Qed.
Lemma lem1993944 : term232 = term58.
Proof. exact (@lem1367765 term61 term61). Qed.
Lemma lem1993945 : term233 = term199.
Proof. exact (@lem706885). Qed.
Lemma lem1993946 : (term233 = term199) = (term234 = term184).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term199). Qed.
Lemma lem1993947 : term234 = term184.
Proof. exact (EQ_MP (@lem1993946) (@lem1993945)). Qed.
Lemma lem1993948 : term184 = term234.
Proof. exact (SYM (@lem1993947)). Qed.
Lemma lem1993949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993950 : term179 = term235.
Proof. exact (MK_COMB (@lem1993949) (@lem1993948)). Qed.
Lemma lem1993951 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem1993952 : term231 = term232.
Proof. exact (MK_COMB (@lem1993951) (@lem1993950)). Qed.
Lemma lem1993953 : term231 = term58.
Proof. exact (TRANS (@lem1993952) (@lem1993944)). Qed.
Lemma lem1993954 : term230 = term58.
Proof. exact (TRANS (@lem1993941) (@lem1993953)). Qed.
Lemma lem1993955 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993956 : term236 = term237.
Proof. exact (MK_COMB (@lem1993955) (@lem1993954)). Qed.
Lemma lem1993957 : term179 = term179.
Proof. exact (eq_refl term179). Qed.
Lemma lem1993958 : term238 = term226.
Proof. exact (MK_COMB (@lem1993956) (@lem1993957)). Qed.
Lemma lem1993960 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993961 : term226 = term227.
Proof. exact (@lem1993960 term61 term184). Qed.
Lemma lem1993962 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993963 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993964 : term229 = term184.
Proof. exact (EQ_MP (@lem1993963) (@lem1993962)). Qed.
Lemma lem1993965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993966 : term227 = term179.
Proof. exact (MK_COMB (@lem1993965) (@lem1993964)). Qed.
Lemma lem1993967 : term226 = term179.
Proof. exact (TRANS (@lem1993961) (@lem1993966)). Qed.
Lemma lem1993968 : term238 = term179.
Proof. exact (TRANS (@lem1993958) (@lem1993967)). Qed.
Lemma lem1993970 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993971 : term196 = term197.
Proof. exact (@lem1993970 term184 term61). Qed.
Lemma lem1993972 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1993973 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1993974 : term200 = term184.
Proof. exact (EQ_MP (@lem1993973) (@lem1993972)). Qed.
Lemma lem1993975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993976 : term197 = term179.
Proof. exact (MK_COMB (@lem1993975) (@lem1993974)). Qed.
Lemma lem1993977 : term196 = term179.
Proof. exact (TRANS (@lem1993971) (@lem1993976)). Qed.
Lemma lem1993978 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem1993979 : term239 = term226.
Proof. exact (MK_COMB (@lem1993978) (@lem1993977)). Qed.
Lemma lem1993981 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1993982 : term226 = term227.
Proof. exact (@lem1993981 term61 term184). Qed.
Lemma lem1993983 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1993984 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1993985 : term229 = term184.
Proof. exact (EQ_MP (@lem1993984) (@lem1993983)). Qed.
Lemma lem1993986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1993987 : term227 = term179.
Proof. exact (MK_COMB (@lem1993986) (@lem1993985)). Qed.
Lemma lem1993988 : term226 = term179.
Proof. exact (TRANS (@lem1993982) (@lem1993987)). Qed.
Lemma lem1993989 : term239 = term179.
Proof. exact (TRANS (@lem1993979) (@lem1993988)). Qed.
Lemma lem1993990 : term179 = term239.
Proof. exact (SYM (@lem1993989)). Qed.
Lemma lem1993991 : term238 = term239.
Proof. exact (TRANS (@lem1993968) (@lem1993990)). Qed.
Lemma lem1993992 : term218 = term183.
Proof. exact (@lem1993919 (@lem1993991)). Qed.
Lemma lem1993995 : term217 = term183.
Proof. exact (TRANS (@lem1993885) (@lem1993992)). Qed.
Lemma lem1993996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1993997 : term240 = term192.
Proof. exact (MK_COMB (@lem1993996) (@lem1993995)). Qed.
Lemma lem1993998 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1993999 (y : real) : (term215 y) = (term213 y).
Proof. exact (MK_COMB (@lem1993997) (@lem1993998 y)). Qed.
Lemma lem1994000 (y : real) : (term214 y) = (term213 y).
Proof. exact (TRANS (@lem1993878 y) (@lem1993999 y)). Qed.
Lemma lem1994001 (x : real) : (term257 x) = (term257 x).
Proof. exact (eq_refl (term257 x)). Qed.
Lemma lem1994002 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1994001 x) (@lem1994000 y)). Qed.
Lemma lem1994003 (x : real) (y : real) : (term259 x y) = (term261 x y).
Proof. exact (TRANS (@lem1993877 x y) (@lem1994002 x y)). Qed.
Lemma lem1994004 (x : real) (y : real) : (term244 x y) = (term261 x y).
Proof. exact (TRANS (@lem1993876 x y) (@lem1994003 x y)). Qed.
Lemma lem1994005 (x : real) (y : real) : (term243 x y) = (term261 x y).
Proof. exact (TRANS (@lem1993789 x y) (@lem1994004 x y)). Qed.
Lemma lem1994006 (x : real) (y : real) : (term242 x y) = (term261 x y).
Proof. exact (TRANS (@lem1993788 x y) (@lem1994005 x y)). Qed.
Lemma lem1994007 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1994008 (x : real) (y : real) : (term262 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem1994007) (@lem1994006 x y)). Qed.
Lemma lem1994009 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994010 (x : real) (y : real) : (term175 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem1994008 x y) (@lem1994009)). Qed.
Lemma lem1994011 (x : real) (y : real) : (term174 x y) = (term264 x y).
Proof. exact (TRANS (@lem1993576 x y) (@lem1994010 x y)). Qed.
Lemma lem1994012 (y : real) (x : real) : (term167 x y) = (term265 y x).
Proof. exact (@lem1988285 (term163 x y) x). Qed.
Lemma lem1994013 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1994015 (x : real) (y : real) : (real_div x y) = (term176 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem1994016 (x : real) (y : real) : (term177 x y) = (term178 x y).
Proof. exact (@lem1994015 (real_sub x y) term179). Qed.
Lemma lem1994021 (n : nat) : (term180 n) = (term181 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem1994023 : term182 = term183.
Proof. exact (@lem1994021 term184). Qed.
Lemma lem1994036 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1994037 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994038 (x : real) (y : real) : (term185 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1994037) (@lem1994036 x y)). Qed.
Lemma lem1994039 (x : real) (y : real) : (term178 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1994038 x y) (@lem1994023)). Qed.
Lemma lem1994040 (x : real) (y : real) : (term187 x y) = (term188 x y).
Proof. exact (@lem1982725 term183 (term19 x y)). Qed.
Lemma lem1994041 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1982781 x term183 (term21 y)). Qed.
Lemma lem1994042 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1982749 term183 term106 y). Qed.
Lemma lem1994044 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1994045 : term106 = term109.
Proof. exact (@lem1994044 term61). Qed.
Lemma lem1994048 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1994049 : term193 = term194.
Proof. exact (MK_COMB (@lem1994048) (@lem1994045)). Qed.
Lemma lem1994050 : term194 = term195.
Proof. exact (@lem1981613 term58 term106 term179 term58). Qed.
Lemma lem1994052 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994053 : term196 = term197.
Proof. exact (@lem1994052 term184 term61). Qed.
Lemma lem1994054 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1994055 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1994056 : term200 = term184.
Proof. exact (EQ_MP (@lem1994055) (@lem1994054)). Qed.
Lemma lem1994057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994058 : term197 = term179.
Proof. exact (MK_COMB (@lem1994057) (@lem1994056)). Qed.
Lemma lem1994059 : term196 = term179.
Proof. exact (TRANS (@lem1994053) (@lem1994058)). Qed.
Lemma lem1994061 (m : nat) (n : nat) : (term201 m n) = (term119 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1994062 : term202 = term121.
Proof. exact (@lem1994061 term61 term61). Qed.
Lemma lem1994063 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994064 : term77 = term61.
Proof. exact (EQ_MP (@lem1994063) (@lem940073)). Qed.
Lemma lem1994065 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994066 : term75 = term58.
Proof. exact (MK_COMB (@lem1994065) (@lem1994064)). Qed.
Lemma lem1994067 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994068 : term121 = term106.
Proof. exact (MK_COMB (@lem1994067) (@lem1994066)). Qed.
Lemma lem1994069 : term202 = term106.
Proof. exact (TRANS (@lem1994062) (@lem1994068)). Qed.
Lemma lem1994070 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1994071 : term203 = term204.
Proof. exact (MK_COMB (@lem1994070) (@lem1994069)). Qed.
Lemma lem1994072 : term195 = term205.
Proof. exact (MK_COMB (@lem1994071) (@lem1994059)). Qed.
Lemma lem1994073 : term194 = term205.
Proof. exact (TRANS (@lem1994050) (@lem1994072)). Qed.
Lemma lem1994076 : term193 = term205.
Proof. exact (TRANS (@lem1994049) (@lem1994073)). Qed.
Lemma lem1994077 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994078 : term206 = term207.
Proof. exact (MK_COMB (@lem1994077) (@lem1994076)). Qed.
Lemma lem1994079 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1994080 (y : real) : (term191 y) = (term208 y).
Proof. exact (MK_COMB (@lem1994078) (@lem1994079 y)). Qed.
Lemma lem1994081 (y : real) : (term190 y) = (term208 y).
Proof. exact (TRANS (@lem1994042 y) (@lem1994080 y)). Qed.
Lemma lem1994084 (x : real) : (term209 x) = (term209 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1994085 (x : real) (y : real) : (term189 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1994084 x) (@lem1994081 y)). Qed.
Lemma lem1994086 (x : real) (y : real) : (term188 x y) = (term210 x y).
Proof. exact (TRANS (@lem1994041 x y) (@lem1994085 x y)). Qed.
Lemma lem1994087 (x : real) (y : real) : (term187 x y) = (term210 x y).
Proof. exact (TRANS (@lem1994040 x y) (@lem1994086 x y)). Qed.
Lemma lem1994088 (x : real) (y : real) : (term178 x y) = (term210 x y).
Proof. exact (TRANS (@lem1994039 x y) (@lem1994087 x y)). Qed.
Lemma lem1994089 (x : real) (y : real) : (term177 x y) = (term210 x y).
Proof. exact (TRANS (@lem1994016 x y) (@lem1994088 x y)). Qed.
Lemma lem1994092 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1994093 (x : real) (y : real) : (term163 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1994092 y) (@lem1994089 x y)). Qed.
Lemma lem1994094 (x : real) (y : real) : (term211 x y) = (term212 x y).
Proof. exact (@lem1982757 (term213 x) y (term208 y)). Qed.
Lemma lem1994095 (y : real) : (term214 y) = (term215 y).
Proof. exact (@lem1982715 term205 y). Qed.
Lemma lem1994097 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994098 : term58 = term60.
Proof. exact (@lem1994097 term61). Qed.
Lemma lem1994101 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1994102 : term217 = term218.
Proof. exact (MK_COMB (@lem1994101) (@lem1994098)). Qed.
Lemma lem1994103 : term219.
Proof. exact (@lem1981473 term106 term179 term58 term58 term58 term179). Qed.
Lemma lem1994105 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994106 : term220 = term221.
Proof. exact (@lem1994105 (NUMERAL 0) term184). Qed.
Lemma lem1994107 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994108 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994109 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994108 h1) (fun h1 : term221 = True => @lem1994107)). Qed.
Lemma lem1994110 : term221 = True.
Proof. exact (EQ_MP (@lem1994109) (@lem1994107)). Qed.
Lemma lem1994111 : term220 = True.
Proof. exact (TRANS (@lem1994106) (@lem1994110)). Qed.
Lemma lem1994112 : True = term220.
Proof. exact (SYM (@lem1994111)). Qed.
Lemma lem1994113 : term220.
Proof. exact (EQ_MP (@lem1994112) (@lem0)). Qed.
Lemma lem1994114 : term223.
Proof. exact (@lem1994103 (@lem1994113)). Qed.
Lemma lem1994116 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994117 : term57 = term68.
Proof. exact (@lem1994116 (NUMERAL 0) term61). Qed.
Lemma lem1994118 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994119 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994120 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994119 h1) (fun h1 : term68 = True => @lem1994118)). Qed.
Lemma lem1994121 : term68 = True.
Proof. exact (EQ_MP (@lem1994120) (@lem1994118)). Qed.
Lemma lem1994122 : term57 = True.
Proof. exact (TRANS (@lem1994117) (@lem1994121)). Qed.
Lemma lem1994123 : True = term57.
Proof. exact (SYM (@lem1994122)). Qed.
Lemma lem1994124 : term57.
Proof. exact (EQ_MP (@lem1994123) (@lem0)). Qed.
Lemma lem1994125 : term224.
Proof. exact (@lem1994114 (@lem1994124)). Qed.
Lemma lem1994127 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994128 : term220 = term221.
Proof. exact (@lem1994127 (NUMERAL 0) term184). Qed.
Lemma lem1994129 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994130 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994131 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994130 h1) (fun h1 : term221 = True => @lem1994129)). Qed.
Lemma lem1994132 : term221 = True.
Proof. exact (EQ_MP (@lem1994131) (@lem1994129)). Qed.
Lemma lem1994133 : term220 = True.
Proof. exact (TRANS (@lem1994128) (@lem1994132)). Qed.
Lemma lem1994134 : True = term220.
Proof. exact (SYM (@lem1994133)). Qed.
Lemma lem1994135 : term220.
Proof. exact (EQ_MP (@lem1994134) (@lem0)). Qed.
Lemma lem1994136 : term225.
Proof. exact (@lem1994125 (@lem1994135)). Qed.
Lemma lem1994138 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994139 : term226 = term227.
Proof. exact (@lem1994138 term61 term184). Qed.
Lemma lem1994140 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994141 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994142 : term229 = term184.
Proof. exact (EQ_MP (@lem1994141) (@lem1994140)). Qed.
Lemma lem1994143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994144 : term227 = term179.
Proof. exact (MK_COMB (@lem1994143) (@lem1994142)). Qed.
Lemma lem1994145 : term226 = term179.
Proof. exact (TRANS (@lem1994139) (@lem1994144)). Qed.
Lemma lem1994147 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1994148 : term120 = term121.
Proof. exact (@lem1994147 term61 term61). Qed.
Lemma lem1994149 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994150 : term77 = term61.
Proof. exact (EQ_MP (@lem1994149) (@lem940073)). Qed.
Lemma lem1994151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994152 : term75 = term58.
Proof. exact (MK_COMB (@lem1994151) (@lem1994150)). Qed.
Lemma lem1994153 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994154 : term121 = term106.
Proof. exact (MK_COMB (@lem1994153) (@lem1994152)). Qed.
Lemma lem1994155 : term120 = term106.
Proof. exact (TRANS (@lem1994148) (@lem1994154)). Qed.
Lemma lem1994156 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1994157 : term122 = term110.
Proof. exact (MK_COMB (@lem1994156) (@lem1994155)). Qed.
Lemma lem1994158 : term230 = term231.
Proof. exact (MK_COMB (@lem1994157) (@lem1994145)). Qed.
Lemma lem1994161 : term232 = term58.
Proof. exact (@lem1367765 term61 term61). Qed.
Lemma lem1994162 : term233 = term199.
Proof. exact (@lem706885). Qed.
Lemma lem1994163 : (term233 = term199) = (term234 = term184).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term199). Qed.
Lemma lem1994164 : term234 = term184.
Proof. exact (EQ_MP (@lem1994163) (@lem1994162)). Qed.
Lemma lem1994165 : term184 = term234.
Proof. exact (SYM (@lem1994164)). Qed.
Lemma lem1994166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994167 : term179 = term235.
Proof. exact (MK_COMB (@lem1994166) (@lem1994165)). Qed.
Lemma lem1994168 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem1994169 : term231 = term232.
Proof. exact (MK_COMB (@lem1994168) (@lem1994167)). Qed.
Lemma lem1994170 : term231 = term58.
Proof. exact (TRANS (@lem1994169) (@lem1994161)). Qed.
Lemma lem1994171 : term230 = term58.
Proof. exact (TRANS (@lem1994158) (@lem1994170)). Qed.
Lemma lem1994172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994173 : term236 = term237.
Proof. exact (MK_COMB (@lem1994172) (@lem1994171)). Qed.
Lemma lem1994174 : term179 = term179.
Proof. exact (eq_refl term179). Qed.
Lemma lem1994175 : term238 = term226.
Proof. exact (MK_COMB (@lem1994173) (@lem1994174)). Qed.
Lemma lem1994177 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994178 : term226 = term227.
Proof. exact (@lem1994177 term61 term184). Qed.
Lemma lem1994179 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994180 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994181 : term229 = term184.
Proof. exact (EQ_MP (@lem1994180) (@lem1994179)). Qed.
Lemma lem1994182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994183 : term227 = term179.
Proof. exact (MK_COMB (@lem1994182) (@lem1994181)). Qed.
Lemma lem1994184 : term226 = term179.
Proof. exact (TRANS (@lem1994178) (@lem1994183)). Qed.
Lemma lem1994185 : term238 = term179.
Proof. exact (TRANS (@lem1994175) (@lem1994184)). Qed.
Lemma lem1994187 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994188 : term196 = term197.
Proof. exact (@lem1994187 term184 term61). Qed.
Lemma lem1994189 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1994190 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1994191 : term200 = term184.
Proof. exact (EQ_MP (@lem1994190) (@lem1994189)). Qed.
Lemma lem1994192 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994193 : term197 = term179.
Proof. exact (MK_COMB (@lem1994192) (@lem1994191)). Qed.
Lemma lem1994194 : term196 = term179.
Proof. exact (TRANS (@lem1994188) (@lem1994193)). Qed.
Lemma lem1994195 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem1994196 : term239 = term226.
Proof. exact (MK_COMB (@lem1994195) (@lem1994194)). Qed.
Lemma lem1994198 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994199 : term226 = term227.
Proof. exact (@lem1994198 term61 term184). Qed.
Lemma lem1994200 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994201 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994202 : term229 = term184.
Proof. exact (EQ_MP (@lem1994201) (@lem1994200)). Qed.
Lemma lem1994203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994204 : term227 = term179.
Proof. exact (MK_COMB (@lem1994203) (@lem1994202)). Qed.
Lemma lem1994205 : term226 = term179.
Proof. exact (TRANS (@lem1994199) (@lem1994204)). Qed.
Lemma lem1994206 : term239 = term179.
Proof. exact (TRANS (@lem1994196) (@lem1994205)). Qed.
Lemma lem1994207 : term179 = term239.
Proof. exact (SYM (@lem1994206)). Qed.
Lemma lem1994208 : term238 = term239.
Proof. exact (TRANS (@lem1994185) (@lem1994207)). Qed.
Lemma lem1994209 : term218 = term183.
Proof. exact (@lem1994136 (@lem1994208)). Qed.
Lemma lem1994212 : term217 = term183.
Proof. exact (TRANS (@lem1994102) (@lem1994209)). Qed.
Lemma lem1994213 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994214 : term240 = term192.
Proof. exact (MK_COMB (@lem1994213) (@lem1994212)). Qed.
Lemma lem1994215 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1994216 (y : real) : (term215 y) = (term213 y).
Proof. exact (MK_COMB (@lem1994214) (@lem1994215 y)). Qed.
Lemma lem1994217 (y : real) : (term214 y) = (term213 y).
Proof. exact (TRANS (@lem1994095 y) (@lem1994216 y)). Qed.
Lemma lem1994218 (x : real) : (term209 x) = (term209 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1994219 (x : real) (y : real) : (term212 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1994218 x) (@lem1994217 y)). Qed.
Lemma lem1994220 (x : real) (y : real) : (term211 x y) = (term241 x y).
Proof. exact (TRANS (@lem1994094 x y) (@lem1994219 x y)). Qed.
Lemma lem1994221 (x : real) (y : real) : (term163 x y) = (term241 x y).
Proof. exact (TRANS (@lem1994093 x y) (@lem1994220 x y)). Qed.
Lemma lem1994222 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1994223 (x : real) (y : real) : (term266 x y) = (term267 x y).
Proof. exact (MK_COMB (@lem1994222) (@lem1994221 x y)). Qed.
Lemma lem1994224 (y : real) (x : real) : (term268 y x) = (term269 y x).
Proof. exact (MK_COMB (@lem1994223 x y) (@lem1994013 x)). Qed.
Lemma lem1994225 (y : real) (x : real) : (term269 y x) = (term270 y x).
Proof. exact (@lem1982792 (term241 x y) x). Qed.
Lemma lem1994229 (x : real) (y : real) : (term270 y x) = (term271 x y).
Proof. exact (@lem1982759 (term213 x) (term21 x) (term213 y)). Qed.
Lemma lem1994230 (x : real) : (term272 x) = (term273 x).
Proof. exact (@lem1982711 term183 term106 x). Qed.
Lemma lem1994232 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1994233 : term106 = term109.
Proof. exact (@lem1994232 term61). Qed.
Lemma lem1994236 : term274 = term274.
Proof. exact (eq_refl term274). Qed.
Lemma lem1994237 : term275 = term276.
Proof. exact (MK_COMB (@lem1994236) (@lem1994233)). Qed.
Lemma lem1994238 : term277.
Proof. exact (@lem1981473 term58 term179 term106 term58 term106 term179). Qed.
Lemma lem1994240 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994241 : term220 = term221.
Proof. exact (@lem1994240 (NUMERAL 0) term184). Qed.
Lemma lem1994242 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994243 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994244 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994243 h1) (fun h1 : term221 = True => @lem1994242)). Qed.
Lemma lem1994245 : term221 = True.
Proof. exact (EQ_MP (@lem1994244) (@lem1994242)). Qed.
Lemma lem1994246 : term220 = True.
Proof. exact (TRANS (@lem1994241) (@lem1994245)). Qed.
Lemma lem1994247 : True = term220.
Proof. exact (SYM (@lem1994246)). Qed.
Lemma lem1994248 : term220.
Proof. exact (EQ_MP (@lem1994247) (@lem0)). Qed.
Lemma lem1994249 : term278.
Proof. exact (@lem1994238 (@lem1994248)). Qed.
Lemma lem1994251 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994252 : term57 = term68.
Proof. exact (@lem1994251 (NUMERAL 0) term61). Qed.
Lemma lem1994253 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994254 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994255 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994254 h1) (fun h1 : term68 = True => @lem1994253)). Qed.
Lemma lem1994256 : term68 = True.
Proof. exact (EQ_MP (@lem1994255) (@lem1994253)). Qed.
Lemma lem1994257 : term57 = True.
Proof. exact (TRANS (@lem1994252) (@lem1994256)). Qed.
Lemma lem1994258 : True = term57.
Proof. exact (SYM (@lem1994257)). Qed.
Lemma lem1994259 : term57.
Proof. exact (EQ_MP (@lem1994258) (@lem0)). Qed.
Lemma lem1994260 : term279.
Proof. exact (@lem1994249 (@lem1994259)). Qed.
Lemma lem1994262 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994263 : term220 = term221.
Proof. exact (@lem1994262 (NUMERAL 0) term184). Qed.
Lemma lem1994264 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994265 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994266 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994265 h1) (fun h1 : term221 = True => @lem1994264)). Qed.
Lemma lem1994267 : term221 = True.
Proof. exact (EQ_MP (@lem1994266) (@lem1994264)). Qed.
Lemma lem1994268 : term220 = True.
Proof. exact (TRANS (@lem1994263) (@lem1994267)). Qed.
Lemma lem1994269 : True = term220.
Proof. exact (SYM (@lem1994268)). Qed.
Lemma lem1994270 : term220.
Proof. exact (EQ_MP (@lem1994269) (@lem0)). Qed.
Lemma lem1994271 : term280.
Proof. exact (@lem1994260 (@lem1994270)). Qed.
Lemma lem1994273 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1994274 : term281 = term282.
Proof. exact (@lem1994273 term61 term184). Qed.
Lemma lem1994275 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994276 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994277 : term229 = term184.
Proof. exact (EQ_MP (@lem1994276) (@lem1994275)). Qed.
Lemma lem1994278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994279 : term227 = term179.
Proof. exact (MK_COMB (@lem1994278) (@lem1994277)). Qed.
Lemma lem1994280 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994281 : term282 = term283.
Proof. exact (MK_COMB (@lem1994280) (@lem1994279)). Qed.
Lemma lem1994282 : term281 = term283.
Proof. exact (TRANS (@lem1994274) (@lem1994281)). Qed.
Lemma lem1994284 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994285 : term74 = term75.
Proof. exact (@lem1994284 term61 term61). Qed.
Lemma lem1994286 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994287 : term77 = term61.
Proof. exact (EQ_MP (@lem1994286) (@lem940073)). Qed.
Lemma lem1994288 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994289 : term75 = term58.
Proof. exact (MK_COMB (@lem1994288) (@lem1994287)). Qed.
Lemma lem1994290 : term74 = term58.
Proof. exact (TRANS (@lem1994285) (@lem1994289)). Qed.
Lemma lem1994291 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1994292 : term284 = term285.
Proof. exact (MK_COMB (@lem1994291) (@lem1994290)). Qed.
Lemma lem1994293 : term286 = term287.
Proof. exact (MK_COMB (@lem1994292) (@lem1994282)). Qed.
Lemma lem1994296 : term288 = term106.
Proof. exact (@lem1367771 term61 term61). Qed.
Lemma lem1994297 : term233 = term199.
Proof. exact (@lem706885). Qed.
Lemma lem1994298 : (term233 = term199) = (term234 = term184).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term199). Qed.
Lemma lem1994299 : term234 = term184.
Proof. exact (EQ_MP (@lem1994298) (@lem1994297)). Qed.
Lemma lem1994300 : term184 = term234.
Proof. exact (SYM (@lem1994299)). Qed.
Lemma lem1994301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994302 : term179 = term235.
Proof. exact (MK_COMB (@lem1994301) (@lem1994300)). Qed.
Lemma lem1994303 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994304 : term283 = term289.
Proof. exact (MK_COMB (@lem1994303) (@lem1994302)). Qed.
Lemma lem1994305 : term285 = term285.
Proof. exact (eq_refl term285). Qed.
Lemma lem1994306 : term287 = term288.
Proof. exact (MK_COMB (@lem1994305) (@lem1994304)). Qed.
Lemma lem1994307 : term287 = term106.
Proof. exact (TRANS (@lem1994306) (@lem1994296)). Qed.
Lemma lem1994308 : term286 = term106.
Proof. exact (TRANS (@lem1994293) (@lem1994307)). Qed.
Lemma lem1994309 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994310 : term290 = term249.
Proof. exact (MK_COMB (@lem1994309) (@lem1994308)). Qed.
Lemma lem1994311 : term179 = term179.
Proof. exact (eq_refl term179). Qed.
Lemma lem1994312 : term291 = term281.
Proof. exact (MK_COMB (@lem1994310) (@lem1994311)). Qed.
Lemma lem1994314 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1994315 : term281 = term282.
Proof. exact (@lem1994314 term61 term184). Qed.
Lemma lem1994316 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994317 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994318 : term229 = term184.
Proof. exact (EQ_MP (@lem1994317) (@lem1994316)). Qed.
Lemma lem1994319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994320 : term227 = term179.
Proof. exact (MK_COMB (@lem1994319) (@lem1994318)). Qed.
Lemma lem1994321 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994322 : term282 = term283.
Proof. exact (MK_COMB (@lem1994321) (@lem1994320)). Qed.
Lemma lem1994323 : term281 = term283.
Proof. exact (TRANS (@lem1994315) (@lem1994322)). Qed.
Lemma lem1994324 : term291 = term283.
Proof. exact (TRANS (@lem1994312) (@lem1994323)). Qed.
Lemma lem1994326 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994327 : term196 = term197.
Proof. exact (@lem1994326 term184 term61). Qed.
Lemma lem1994328 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1994329 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1994330 : term200 = term184.
Proof. exact (EQ_MP (@lem1994329) (@lem1994328)). Qed.
Lemma lem1994331 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994332 : term197 = term179.
Proof. exact (MK_COMB (@lem1994331) (@lem1994330)). Qed.
Lemma lem1994333 : term196 = term179.
Proof. exact (TRANS (@lem1994327) (@lem1994332)). Qed.
Lemma lem1994334 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem1994335 : term292 = term281.
Proof. exact (MK_COMB (@lem1994334) (@lem1994333)). Qed.
Lemma lem1994337 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1994338 : term281 = term282.
Proof. exact (@lem1994337 term61 term184). Qed.
Lemma lem1994339 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994340 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994341 : term229 = term184.
Proof. exact (EQ_MP (@lem1994340) (@lem1994339)). Qed.
Lemma lem1994342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994343 : term227 = term179.
Proof. exact (MK_COMB (@lem1994342) (@lem1994341)). Qed.
Lemma lem1994344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994345 : term282 = term283.
Proof. exact (MK_COMB (@lem1994344) (@lem1994343)). Qed.
Lemma lem1994346 : term281 = term283.
Proof. exact (TRANS (@lem1994338) (@lem1994345)). Qed.
Lemma lem1994347 : term292 = term283.
Proof. exact (TRANS (@lem1994335) (@lem1994346)). Qed.
Lemma lem1994348 : term283 = term292.
Proof. exact (SYM (@lem1994347)). Qed.
Lemma lem1994349 : term291 = term292.
Proof. exact (TRANS (@lem1994324) (@lem1994348)). Qed.
Lemma lem1994350 : term276 = term205.
Proof. exact (@lem1994271 (@lem1994349)). Qed.
Lemma lem1994353 : term275 = term205.
Proof. exact (TRANS (@lem1994237) (@lem1994350)). Qed.
Lemma lem1994354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994355 : term293 = term207.
Proof. exact (MK_COMB (@lem1994354) (@lem1994353)). Qed.
Lemma lem1994356 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1994357 (x : real) : (term273 x) = (term208 x).
Proof. exact (MK_COMB (@lem1994355) (@lem1994356 x)). Qed.
Lemma lem1994358 (x : real) : (term272 x) = (term208 x).
Proof. exact (TRANS (@lem1994230 x) (@lem1994357 x)). Qed.
Lemma lem1994359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1994360 (x : real) : (term294 x) = (term257 x).
Proof. exact (MK_COMB (@lem1994359) (@lem1994358 x)). Qed.
Lemma lem1994361 (y : real) : (term213 y) = (term213 y).
Proof. exact (eq_refl (term213 y)). Qed.
Lemma lem1994362 (x : real) (y : real) : (term271 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1994360 x) (@lem1994361 y)). Qed.
Lemma lem1994364 (x : real) (y : real) : (term270 y x) = (term261 x y).
Proof. exact (TRANS (@lem1994229 x y) (@lem1994362 x y)). Qed.
Lemma lem1994365 (x : real) (y : real) : (term269 y x) = (term261 x y).
Proof. exact (TRANS (@lem1994225 y x) (@lem1994364 x y)). Qed.
Lemma lem1994366 (x : real) (y : real) : (term268 y x) = (term261 x y).
Proof. exact (TRANS (@lem1994224 y x) (@lem1994365 x y)). Qed.
Lemma lem1994367 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1994368 (x : real) (y : real) : (term295 y x) = (term296 x y).
Proof. exact (MK_COMB (@lem1994367) (@lem1994366 x y)). Qed.
Lemma lem1994369 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994370 (x : real) (y : real) : (term265 y x) = (term297 x y).
Proof. exact (MK_COMB (@lem1994368 x y) (@lem1994369)). Qed.
Lemma lem1994371 (x : real) (y : real) : (term167 x y) = (term297 x y).
Proof. exact (TRANS (@lem1994012 y x) (@lem1994370 x y)). Qed.
Lemma lem1994372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1994373 (x : real) (y : real) : (term298 x y) = (term299 x y).
Proof. exact (MK_COMB (@lem1994372) (@lem1994011 x y)). Qed.
Lemma lem1994374 (x : real) (y : real) : (term165 x y) = (term300 x y).
Proof. exact (MK_COMB (@lem1994373 x y) (@lem1994371 x y)). Qed.
Lemma lem1994375 (x : real) (y : real) : (term168 x y) = (term26 x y).
Proof. exact (@lem1988297 x y). Qed.
Lemma lem1994388 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1994389 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1994390 (x : real) (y : real) : (term27 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1994389) (@lem1994388 x y)). Qed.
Lemma lem1994391 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994392 (x : real) (y : real) : (term26 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1994390 x y) (@lem1994391)). Qed.
Lemma lem1994393 (x : real) (y : real) : (term168 x y) = (term136 x y).
Proof. exact (TRANS (@lem1994375 x y) (@lem1994392 x y)). Qed.
Lemma lem1994394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1994395 (x : real) (y : real) : (term170 x y) = (term301 x y).
Proof. exact (MK_COMB (@lem1994394) (@lem1994374 x y)). Qed.
Lemma lem1994396 (x : real) (y : real) : (term172 x y) = (term302 x y).
Proof. exact (MK_COMB (@lem1994395 x y) (@lem1994393 x y)). Qed.
Lemma lem1994403 (x : real) (y : real) : (term173 x y) = (term302 x y).
Proof. exact (TRANS (@lem1993575 x y) (@lem1994396 x y)). Qed.
Lemma lem1994420 (x : real) (y : real) : (term302 x y) = (term303 x y).
Proof. exact (@lem19367 (term264 x y) (term297 x y) (term136 x y)). Qed.
Lemma lem1994421 (x : real) (y : real) : (term173 x y) = (term303 x y).
Proof. exact (TRANS (@lem1994403 x y) (@lem1994420 x y)). Qed.
Lemma lem1994431 (x : real) (y : real) (h1 : term303 x y) : term303 x y.
Proof. exact (h1). Qed.
Lemma lem1994432 (x : real) (y : real) (h1 : term304 x y) : term304 x y.
Proof. exact (h1). Qed.
Lemma lem1994433 (x : real) (y : real) (h1 : term304 x y) : term136 x y.
Proof. exact (proj2 (@lem1994432 x y h1)). Qed.
Lemma lem1994434 (x : real) (y : real) (h1 : term304 x y) : term264 x y.
Proof. exact (proj1 (@lem1994432 x y h1)). Qed.
Lemma lem1994436 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1994437 : term56 = term57.
Proof. exact (@lem1994436 term24 term58). Qed.
Lemma lem1994439 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994440 : term58 = term60.
Proof. exact (@lem1994439 term61). Qed.
Lemma lem1994442 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994443 : term24 = term62.
Proof. exact (@lem1994442 (NUMERAL 0)). Qed.
Lemma lem1994444 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994445 : term63 = term64.
Proof. exact (MK_COMB (@lem1994444) (@lem1994443)). Qed.
Lemma lem1994446 : term57 = term65.
Proof. exact (MK_COMB (@lem1994445) (@lem1994440)). Qed.
Lemma lem1994447 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1994449 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994450 : term57 = term68.
Proof. exact (@lem1994449 (NUMERAL 0) term61). Qed.
Lemma lem1994451 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994452 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994453 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994452 h1) (fun h1 : term68 = True => @lem1994451)). Qed.
Lemma lem1994454 : term68 = True.
Proof. exact (EQ_MP (@lem1994453) (@lem1994451)). Qed.
Lemma lem1994455 : term57 = True.
Proof. exact (TRANS (@lem1994450) (@lem1994454)). Qed.
Lemma lem1994456 : True = term57.
Proof. exact (SYM (@lem1994455)). Qed.
Lemma lem1994457 : term57.
Proof. exact (EQ_MP (@lem1994456) (@lem0)). Qed.
Lemma lem1994458 : term70.
Proof. exact (@lem1994447 (@lem1994457)). Qed.
Lemma lem1994460 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994461 : term57 = term68.
Proof. exact (@lem1994460 (NUMERAL 0) term61). Qed.
Lemma lem1994462 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994463 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994464 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994463 h1) (fun h1 : term68 = True => @lem1994462)). Qed.
Lemma lem1994465 : term68 = True.
Proof. exact (EQ_MP (@lem1994464) (@lem1994462)). Qed.
Lemma lem1994466 : term57 = True.
Proof. exact (TRANS (@lem1994461) (@lem1994465)). Qed.
Lemma lem1994467 : True = term57.
Proof. exact (SYM (@lem1994466)). Qed.
Lemma lem1994468 : term57.
Proof. exact (EQ_MP (@lem1994467) (@lem0)). Qed.
Lemma lem1994469 : term65 = term71.
Proof. exact (@lem1994458 (@lem1994468)). Qed.
Lemma lem1994471 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994472 : term74 = term75.
Proof. exact (@lem1994471 term61 term61). Qed.
Lemma lem1994473 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994474 : term77 = term61.
Proof. exact (EQ_MP (@lem1994473) (@lem940073)). Qed.
Lemma lem1994475 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994476 : term75 = term58.
Proof. exact (MK_COMB (@lem1994475) (@lem1994474)). Qed.
Lemma lem1994477 : term74 = term58.
Proof. exact (TRANS (@lem1994472) (@lem1994476)). Qed.
Lemma lem1994479 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994480 : term79 = term24.
Proof. exact (@lem1994479 term61). Qed.
Lemma lem1994481 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994482 : term80 = term63.
Proof. exact (MK_COMB (@lem1994481) (@lem1994480)). Qed.
Lemma lem1994483 : term71 = term57.
Proof. exact (MK_COMB (@lem1994482) (@lem1994477)). Qed.
Lemma lem1994485 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994486 : term57 = term68.
Proof. exact (@lem1994485 (NUMERAL 0) term61). Qed.
Lemma lem1994487 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994488 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994489 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994488 h1) (fun h1 : term68 = True => @lem1994487)). Qed.
Lemma lem1994490 : term68 = True.
Proof. exact (EQ_MP (@lem1994489) (@lem1994487)). Qed.
Lemma lem1994491 : term57 = True.
Proof. exact (TRANS (@lem1994486) (@lem1994490)). Qed.
Lemma lem1994492 : term71 = True.
Proof. exact (TRANS (@lem1994483) (@lem1994491)). Qed.
Lemma lem1994493 : term65 = True.
Proof. exact (TRANS (@lem1994469) (@lem1994492)). Qed.
Lemma lem1994494 : term57 = True.
Proof. exact (TRANS (@lem1994446) (@lem1994493)). Qed.
Lemma lem1994495 : term56 = True.
Proof. exact (TRANS (@lem1994437) (@lem1994494)). Qed.
Lemma lem1994496 : True = term56.
Proof. exact (SYM (@lem1994495)). Qed.
Lemma lem1994497 : term56.
Proof. exact (EQ_MP (@lem1994496) (@lem0)). Qed.
Lemma lem1994498 (x : real) (y : real) (h1 : term304 x y) : term305 x y.
Proof. exact (conj (@lem1994497) (@lem1994434 x y h1)). Qed.
Lemma lem1994500 (x : real) (y : real) : term82 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1994501 (x : real) (y : real) : term306 x y.
Proof. exact (@lem1994500 term58 (term261 x y)). Qed.
Lemma lem1994502 (x : real) (y : real) (h1 : term304 x y) : term307 x y.
Proof. exact (@lem1994501 x y (@lem1994498 x y h1)). Qed.
Lemma lem1994503 (x : real) (y : real) : (term308 x y) = (term261 x y).
Proof. exact (@lem1982733 (term261 x y)). Qed.
Lemma lem1994504 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1994505 (x : real) (y : real) : (term309 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem1994504) (@lem1994503 x y)). Qed.
Lemma lem1994506 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994507 (x : real) (y : real) : (term307 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem1994505 x y) (@lem1994506)). Qed.
Lemma lem1994508 (x : real) (y : real) (h1 : term304 x y) : term264 x y.
Proof. exact (EQ_MP (@lem1994507 x y) (@lem1994502 x y h1)). Qed.
Lemma lem1994510 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1994511 : term310 = term311.
Proof. exact (@lem1994510 term24 term183). Qed.
Lemma lem1994512 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1994514 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994515 : term24 = term62.
Proof. exact (@lem1994514 (NUMERAL 0)). Qed.
Lemma lem1994516 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994517 : term63 = term64.
Proof. exact (MK_COMB (@lem1994516) (@lem1994515)). Qed.
Lemma lem1994518 : term311 = term312.
Proof. exact (MK_COMB (@lem1994517) (@lem1994512)). Qed.
Lemma lem1994519 : term313.
Proof. exact (@lem1980255 term24 term179 term58 term58). Qed.
Lemma lem1994521 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994522 : term57 = term68.
Proof. exact (@lem1994521 (NUMERAL 0) term61). Qed.
Lemma lem1994523 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994524 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994525 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994524 h1) (fun h1 : term68 = True => @lem1994523)). Qed.
Lemma lem1994526 : term68 = True.
Proof. exact (EQ_MP (@lem1994525) (@lem1994523)). Qed.
Lemma lem1994527 : term57 = True.
Proof. exact (TRANS (@lem1994522) (@lem1994526)). Qed.
Lemma lem1994528 : True = term57.
Proof. exact (SYM (@lem1994527)). Qed.
Lemma lem1994529 : term57.
Proof. exact (EQ_MP (@lem1994528) (@lem0)). Qed.
Lemma lem1994530 : term314.
Proof. exact (@lem1994519 (@lem1994529)). Qed.
Lemma lem1994532 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994533 : term220 = term221.
Proof. exact (@lem1994532 (NUMERAL 0) term184). Qed.
Lemma lem1994534 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994535 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994536 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994535 h1) (fun h1 : term221 = True => @lem1994534)). Qed.
Lemma lem1994537 : term221 = True.
Proof. exact (EQ_MP (@lem1994536) (@lem1994534)). Qed.
Lemma lem1994538 : term220 = True.
Proof. exact (TRANS (@lem1994533) (@lem1994537)). Qed.
Lemma lem1994539 : True = term220.
Proof. exact (SYM (@lem1994538)). Qed.
Lemma lem1994540 : term220.
Proof. exact (EQ_MP (@lem1994539) (@lem0)). Qed.
Lemma lem1994541 : term312 = term315.
Proof. exact (@lem1994530 (@lem1994540)). Qed.
Lemma lem1994543 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994544 : term74 = term75.
Proof. exact (@lem1994543 term61 term61). Qed.
Lemma lem1994545 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994546 : term77 = term61.
Proof. exact (EQ_MP (@lem1994545) (@lem940073)). Qed.
Lemma lem1994547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994548 : term75 = term58.
Proof. exact (MK_COMB (@lem1994547) (@lem1994546)). Qed.
Lemma lem1994549 : term74 = term58.
Proof. exact (TRANS (@lem1994544) (@lem1994548)). Qed.
Lemma lem1994551 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994552 : term316 = term24.
Proof. exact (@lem1994551 term184). Qed.
Lemma lem1994553 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994554 : term317 = term63.
Proof. exact (MK_COMB (@lem1994553) (@lem1994552)). Qed.
Lemma lem1994555 : term315 = term57.
Proof. exact (MK_COMB (@lem1994554) (@lem1994549)). Qed.
Lemma lem1994557 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994558 : term57 = term68.
Proof. exact (@lem1994557 (NUMERAL 0) term61). Qed.
Lemma lem1994559 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994560 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994561 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994560 h1) (fun h1 : term68 = True => @lem1994559)). Qed.
Lemma lem1994562 : term68 = True.
Proof. exact (EQ_MP (@lem1994561) (@lem1994559)). Qed.
Lemma lem1994563 : term57 = True.
Proof. exact (TRANS (@lem1994558) (@lem1994562)). Qed.
Lemma lem1994564 : term315 = True.
Proof. exact (TRANS (@lem1994555) (@lem1994563)). Qed.
Lemma lem1994565 : term312 = True.
Proof. exact (TRANS (@lem1994541) (@lem1994564)). Qed.
Lemma lem1994566 : term311 = True.
Proof. exact (TRANS (@lem1994518) (@lem1994565)). Qed.
Lemma lem1994567 : term310 = True.
Proof. exact (TRANS (@lem1994511) (@lem1994566)). Qed.
Lemma lem1994568 : True = term310.
Proof. exact (SYM (@lem1994567)). Qed.
Lemma lem1994569 : term310.
Proof. exact (EQ_MP (@lem1994568) (@lem0)). Qed.
Lemma lem1994570 (x : real) (y : real) (h1 : term304 x y) : term318 x y.
Proof. exact (conj (@lem1994569) (@lem1994433 x y h1)). Qed.
Lemma lem1994572 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1994573 (x : real) (y : real) : term319 x y.
Proof. exact (@lem1994572 term183 (term19 x y)). Qed.
Lemma lem1994574 (x : real) (y : real) (h1 : term304 x y) : term320 x y.
Proof. exact (@lem1994573 x y (@lem1994570 x y h1)). Qed.
Lemma lem1994575 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1982781 x term183 (term21 y)). Qed.
Lemma lem1994576 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1982749 term183 term106 y). Qed.
Lemma lem1994578 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1994579 : term106 = term109.
Proof. exact (@lem1994578 term61). Qed.
Lemma lem1994582 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1994583 : term193 = term194.
Proof. exact (MK_COMB (@lem1994582) (@lem1994579)). Qed.
Lemma lem1994584 : term194 = term195.
Proof. exact (@lem1981613 term58 term106 term179 term58). Qed.
Lemma lem1994586 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994587 : term196 = term197.
Proof. exact (@lem1994586 term184 term61). Qed.
Lemma lem1994588 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1994589 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1994590 : term200 = term184.
Proof. exact (EQ_MP (@lem1994589) (@lem1994588)). Qed.
Lemma lem1994591 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994592 : term197 = term179.
Proof. exact (MK_COMB (@lem1994591) (@lem1994590)). Qed.
Lemma lem1994593 : term196 = term179.
Proof. exact (TRANS (@lem1994587) (@lem1994592)). Qed.
Lemma lem1994595 (m : nat) (n : nat) : (term201 m n) = (term119 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1994596 : term202 = term121.
Proof. exact (@lem1994595 term61 term61). Qed.
Lemma lem1994597 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994598 : term77 = term61.
Proof. exact (EQ_MP (@lem1994597) (@lem940073)). Qed.
Lemma lem1994599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994600 : term75 = term58.
Proof. exact (MK_COMB (@lem1994599) (@lem1994598)). Qed.
Lemma lem1994601 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994602 : term121 = term106.
Proof. exact (MK_COMB (@lem1994601) (@lem1994600)). Qed.
Lemma lem1994603 : term202 = term106.
Proof. exact (TRANS (@lem1994596) (@lem1994602)). Qed.
Lemma lem1994604 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1994605 : term203 = term204.
Proof. exact (MK_COMB (@lem1994604) (@lem1994603)). Qed.
Lemma lem1994606 : term195 = term205.
Proof. exact (MK_COMB (@lem1994605) (@lem1994593)). Qed.
Lemma lem1994607 : term194 = term205.
Proof. exact (TRANS (@lem1994584) (@lem1994606)). Qed.
Lemma lem1994610 : term193 = term205.
Proof. exact (TRANS (@lem1994583) (@lem1994607)). Qed.
Lemma lem1994611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994612 : term206 = term207.
Proof. exact (MK_COMB (@lem1994611) (@lem1994610)). Qed.
Lemma lem1994613 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1994614 (y : real) : (term191 y) = (term208 y).
Proof. exact (MK_COMB (@lem1994612) (@lem1994613 y)). Qed.
Lemma lem1994615 (y : real) : (term190 y) = (term208 y).
Proof. exact (TRANS (@lem1994576 y) (@lem1994614 y)). Qed.
Lemma lem1994618 (x : real) : (term209 x) = (term209 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1994619 (x : real) (y : real) : (term189 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1994618 x) (@lem1994615 y)). Qed.
Lemma lem1994620 (x : real) (y : real) : (term188 x y) = (term210 x y).
Proof. exact (TRANS (@lem1994575 x y) (@lem1994619 x y)). Qed.
Lemma lem1994621 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1994622 (x : real) (y : real) : (term321 x y) = (term322 x y).
Proof. exact (MK_COMB (@lem1994621) (@lem1994620 x y)). Qed.
Lemma lem1994623 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994624 (x : real) (y : real) : (term320 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1994622 x y) (@lem1994623)). Qed.
Lemma lem1994625 (x : real) (y : real) (h1 : term304 x y) : term323 x y.
Proof. exact (EQ_MP (@lem1994624 x y) (@lem1994574 x y h1)). Qed.
Lemma lem1994626 (x : real) (y : real) (h1 : term304 x y) : term324 x y.
Proof. exact (conj (@lem1994625 x y h1) (@lem1994508 x y h1)). Qed.
Lemma lem1994628 (x : real) (y : real) : term97 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1994629 (x : real) (y : real) : term325 x y.
Proof. exact (@lem1994628 (term210 x y) (term261 x y)). Qed.
Lemma lem1994630 (x : real) (y : real) (h1 : term304 x y) : term326 x y.
Proof. exact (@lem1994629 x y (@lem1994626 x y h1)). Qed.
Lemma lem1994631 (x : real) (y : real) : (term327 x y) = (term328 x y).
Proof. exact (@lem1982753 (term213 x) (term208 x) (term208 y) (term213 y)). Qed.
Lemma lem1994632 (x : real) : (term329 x) = (term330 x).
Proof. exact (@lem1982711 term183 term205 x). Qed.
Lemma lem1994638 : term331.
Proof. exact (@lem1981473 term58 term179 term106 term179 term24 term58). Qed.
Lemma lem1994640 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994641 : term220 = term221.
Proof. exact (@lem1994640 (NUMERAL 0) term184). Qed.
Lemma lem1994642 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994643 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994644 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994643 h1) (fun h1 : term221 = True => @lem1994642)). Qed.
Lemma lem1994645 : term221 = True.
Proof. exact (EQ_MP (@lem1994644) (@lem1994642)). Qed.
Lemma lem1994646 : term220 = True.
Proof. exact (TRANS (@lem1994641) (@lem1994645)). Qed.
Lemma lem1994647 : True = term220.
Proof. exact (SYM (@lem1994646)). Qed.
Lemma lem1994648 : term220.
Proof. exact (EQ_MP (@lem1994647) (@lem0)). Qed.
Lemma lem1994649 : term332.
Proof. exact (@lem1994638 (@lem1994648)). Qed.
Lemma lem1994651 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994652 : term220 = term221.
Proof. exact (@lem1994651 (NUMERAL 0) term184). Qed.
Lemma lem1994653 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994654 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994655 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994654 h1) (fun h1 : term221 = True => @lem1994653)). Qed.
Lemma lem1994656 : term221 = True.
Proof. exact (EQ_MP (@lem1994655) (@lem1994653)). Qed.
Lemma lem1994657 : term220 = True.
Proof. exact (TRANS (@lem1994652) (@lem1994656)). Qed.
Lemma lem1994658 : True = term220.
Proof. exact (SYM (@lem1994657)). Qed.
Lemma lem1994659 : term220.
Proof. exact (EQ_MP (@lem1994658) (@lem0)). Qed.
Lemma lem1994660 : term333.
Proof. exact (@lem1994649 (@lem1994659)). Qed.
Lemma lem1994662 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994663 : term57 = term68.
Proof. exact (@lem1994662 (NUMERAL 0) term61). Qed.
Lemma lem1994664 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994665 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994666 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994665 h1) (fun h1 : term68 = True => @lem1994664)). Qed.
Lemma lem1994667 : term68 = True.
Proof. exact (EQ_MP (@lem1994666) (@lem1994664)). Qed.
Lemma lem1994668 : term57 = True.
Proof. exact (TRANS (@lem1994663) (@lem1994667)). Qed.
Lemma lem1994669 : True = term57.
Proof. exact (SYM (@lem1994668)). Qed.
Lemma lem1994670 : term57.
Proof. exact (EQ_MP (@lem1994669) (@lem0)). Qed.
Lemma lem1994671 : term334.
Proof. exact (@lem1994660 (@lem1994670)). Qed.
Lemma lem1994673 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1994674 : term281 = term282.
Proof. exact (@lem1994673 term61 term184). Qed.
Lemma lem1994675 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994676 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994677 : term229 = term184.
Proof. exact (EQ_MP (@lem1994676) (@lem1994675)). Qed.
Lemma lem1994678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994679 : term227 = term179.
Proof. exact (MK_COMB (@lem1994678) (@lem1994677)). Qed.
Lemma lem1994680 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994681 : term282 = term283.
Proof. exact (MK_COMB (@lem1994680) (@lem1994679)). Qed.
Lemma lem1994682 : term281 = term283.
Proof. exact (TRANS (@lem1994674) (@lem1994681)). Qed.
Lemma lem1994684 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994685 : term226 = term227.
Proof. exact (@lem1994684 term61 term184). Qed.
Lemma lem1994686 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994687 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994688 : term229 = term184.
Proof. exact (EQ_MP (@lem1994687) (@lem1994686)). Qed.
Lemma lem1994689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994690 : term227 = term179.
Proof. exact (MK_COMB (@lem1994689) (@lem1994688)). Qed.
Lemma lem1994691 : term226 = term179.
Proof. exact (TRANS (@lem1994685) (@lem1994690)). Qed.
Lemma lem1994692 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1994693 : term335 = term336.
Proof. exact (MK_COMB (@lem1994692) (@lem1994691)). Qed.
Lemma lem1994694 : term337 = term338.
Proof. exact (MK_COMB (@lem1994693) (@lem1994682)). Qed.
Lemma lem1994696 (m : nat) : (term339 m) = term24.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1994697 : term338 = term24.
Proof. exact (@lem1994696 term184). Qed.
Lemma lem1994698 : term337 = term24.
Proof. exact (TRANS (@lem1994694) (@lem1994697)). Qed.
Lemma lem1994699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994700 : term340 = term126.
Proof. exact (MK_COMB (@lem1994699) (@lem1994698)). Qed.
Lemma lem1994701 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1994702 : term341 = term79.
Proof. exact (MK_COMB (@lem1994700) (@lem1994701)). Qed.
Lemma lem1994704 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994705 : term79 = term24.
Proof. exact (@lem1994704 term61). Qed.
Lemma lem1994706 : term341 = term24.
Proof. exact (TRANS (@lem1994702) (@lem1994705)). Qed.
Lemma lem1994708 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994709 : term342 = term343.
Proof. exact (@lem1994708 term184 term184). Qed.
Lemma lem1994710 : (term76 = (BIT1 0)) = (term344 = term345).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994711 : term344 = term345.
Proof. exact (EQ_MP (@lem1994710) (@lem940073)). Qed.
Lemma lem1994712 : (term344 = term345) = (term346 = term347).
Proof. exact (@lem1008952 term199 term345). Qed.
Lemma lem1994713 : term346 = term347.
Proof. exact (EQ_MP (@lem1994712) (@lem1994711)). Qed.
Lemma lem1994714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994715 : term343 = term348.
Proof. exact (MK_COMB (@lem1994714) (@lem1994713)). Qed.
Lemma lem1994716 : term342 = term348.
Proof. exact (TRANS (@lem1994709) (@lem1994715)). Qed.
Lemma lem1994717 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1994718 : term349 = term350.
Proof. exact (MK_COMB (@lem1994717) (@lem1994716)). Qed.
Lemma lem1994720 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994721 : term350 = term24.
Proof. exact (@lem1994720 term347). Qed.
Lemma lem1994722 : term349 = term24.
Proof. exact (TRANS (@lem1994718) (@lem1994721)). Qed.
Lemma lem1994723 : term24 = term349.
Proof. exact (SYM (@lem1994722)). Qed.
Lemma lem1994724 : term341 = term349.
Proof. exact (TRANS (@lem1994706) (@lem1994723)). Qed.
Lemma lem1994726 : term351 = term62.
Proof. exact (@lem1994671 (@lem1994724)). Qed.
Lemma lem1994728 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1994729 : term62 = term24.
Proof. exact (@lem1994728 term24). Qed.
Lemma lem1994730 : term351 = term24.
Proof. exact (TRANS (@lem1994726) (@lem1994729)). Qed.
Lemma lem1994731 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994732 : term352 = term126.
Proof. exact (MK_COMB (@lem1994731) (@lem1994730)). Qed.
Lemma lem1994733 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1994734 (x : real) : (term330 x) = (term131 x).
Proof. exact (MK_COMB (@lem1994732) (@lem1994733 x)). Qed.
Lemma lem1994735 (x : real) : (term329 x) = (term131 x).
Proof. exact (TRANS (@lem1994632 x) (@lem1994734 x)). Qed.
Lemma lem1994736 (x : real) : (term131 x) = term24.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1994737 (x : real) : (term329 x) = term24.
Proof. exact (TRANS (@lem1994735 x) (@lem1994736 x)). Qed.
Lemma lem1994738 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1994739 (x : real) : (term353 x) = term147.
Proof. exact (MK_COMB (@lem1994738) (@lem1994737 x)). Qed.
Lemma lem1994740 (y : real) : (term354 y) = (term355 y).
Proof. exact (@lem1982711 term205 term183 y). Qed.
Lemma lem1994746 : term356.
Proof. exact (@lem1981473 term106 term179 term58 term179 term24 term58). Qed.
Lemma lem1994748 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994749 : term220 = term221.
Proof. exact (@lem1994748 (NUMERAL 0) term184). Qed.
Lemma lem1994750 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994751 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994752 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994751 h1) (fun h1 : term221 = True => @lem1994750)). Qed.
Lemma lem1994753 : term221 = True.
Proof. exact (EQ_MP (@lem1994752) (@lem1994750)). Qed.
Lemma lem1994754 : term220 = True.
Proof. exact (TRANS (@lem1994749) (@lem1994753)). Qed.
Lemma lem1994755 : True = term220.
Proof. exact (SYM (@lem1994754)). Qed.
Lemma lem1994756 : term220.
Proof. exact (EQ_MP (@lem1994755) (@lem0)). Qed.
Lemma lem1994757 : term357.
Proof. exact (@lem1994746 (@lem1994756)). Qed.
Lemma lem1994759 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994760 : term220 = term221.
Proof. exact (@lem1994759 (NUMERAL 0) term184). Qed.
Lemma lem1994761 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1994762 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1994763 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1994762 h1) (fun h1 : term221 = True => @lem1994761)). Qed.
Lemma lem1994764 : term221 = True.
Proof. exact (EQ_MP (@lem1994763) (@lem1994761)). Qed.
Lemma lem1994765 : term220 = True.
Proof. exact (TRANS (@lem1994760) (@lem1994764)). Qed.
Lemma lem1994766 : True = term220.
Proof. exact (SYM (@lem1994765)). Qed.
Lemma lem1994767 : term220.
Proof. exact (EQ_MP (@lem1994766) (@lem0)). Qed.
Lemma lem1994768 : term358.
Proof. exact (@lem1994757 (@lem1994767)). Qed.
Lemma lem1994770 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994771 : term57 = term68.
Proof. exact (@lem1994770 (NUMERAL 0) term61). Qed.
Lemma lem1994772 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994773 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994774 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994773 h1) (fun h1 : term68 = True => @lem1994772)). Qed.
Lemma lem1994775 : term68 = True.
Proof. exact (EQ_MP (@lem1994774) (@lem1994772)). Qed.
Lemma lem1994776 : term57 = True.
Proof. exact (TRANS (@lem1994771) (@lem1994775)). Qed.
Lemma lem1994777 : True = term57.
Proof. exact (SYM (@lem1994776)). Qed.
Lemma lem1994778 : term57.
Proof. exact (EQ_MP (@lem1994777) (@lem0)). Qed.
Lemma lem1994779 : term359.
Proof. exact (@lem1994768 (@lem1994778)). Qed.
Lemma lem1994781 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994782 : term226 = term227.
Proof. exact (@lem1994781 term61 term184). Qed.
Lemma lem1994783 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994784 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994785 : term229 = term184.
Proof. exact (EQ_MP (@lem1994784) (@lem1994783)). Qed.
Lemma lem1994786 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994787 : term227 = term179.
Proof. exact (MK_COMB (@lem1994786) (@lem1994785)). Qed.
Lemma lem1994788 : term226 = term179.
Proof. exact (TRANS (@lem1994782) (@lem1994787)). Qed.
Lemma lem1994790 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1994791 : term281 = term282.
Proof. exact (@lem1994790 term61 term184). Qed.
Lemma lem1994792 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1994793 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1994794 : term229 = term184.
Proof. exact (EQ_MP (@lem1994793) (@lem1994792)). Qed.
Lemma lem1994795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994796 : term227 = term179.
Proof. exact (MK_COMB (@lem1994795) (@lem1994794)). Qed.
Lemma lem1994797 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1994798 : term282 = term283.
Proof. exact (MK_COMB (@lem1994797) (@lem1994796)). Qed.
Lemma lem1994799 : term281 = term283.
Proof. exact (TRANS (@lem1994791) (@lem1994798)). Qed.
Lemma lem1994800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1994801 : term360 = term361.
Proof. exact (MK_COMB (@lem1994800) (@lem1994799)). Qed.
Lemma lem1994802 : term362 = term363.
Proof. exact (MK_COMB (@lem1994801) (@lem1994788)). Qed.
Lemma lem1994804 (m : nat) : (term124 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1994805 : term363 = term24.
Proof. exact (@lem1994804 term184). Qed.
Lemma lem1994806 : term362 = term24.
Proof. exact (TRANS (@lem1994802) (@lem1994805)). Qed.
Lemma lem1994807 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994808 : term364 = term126.
Proof. exact (MK_COMB (@lem1994807) (@lem1994806)). Qed.
Lemma lem1994809 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1994810 : term365 = term79.
Proof. exact (MK_COMB (@lem1994808) (@lem1994809)). Qed.
Lemma lem1994812 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994813 : term79 = term24.
Proof. exact (@lem1994812 term61). Qed.
Lemma lem1994814 : term365 = term24.
Proof. exact (TRANS (@lem1994810) (@lem1994813)). Qed.
Lemma lem1994816 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994817 : term342 = term343.
Proof. exact (@lem1994816 term184 term184). Qed.
Lemma lem1994818 : (term76 = (BIT1 0)) = (term344 = term345).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994819 : term344 = term345.
Proof. exact (EQ_MP (@lem1994818) (@lem940073)). Qed.
Lemma lem1994820 : (term344 = term345) = (term346 = term347).
Proof. exact (@lem1008952 term199 term345). Qed.
Lemma lem1994821 : term346 = term347.
Proof. exact (EQ_MP (@lem1994820) (@lem1994819)). Qed.
Lemma lem1994822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994823 : term343 = term348.
Proof. exact (MK_COMB (@lem1994822) (@lem1994821)). Qed.
Lemma lem1994824 : term342 = term348.
Proof. exact (TRANS (@lem1994817) (@lem1994823)). Qed.
Lemma lem1994825 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1994826 : term349 = term350.
Proof. exact (MK_COMB (@lem1994825) (@lem1994824)). Qed.
Lemma lem1994828 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994829 : term350 = term24.
Proof. exact (@lem1994828 term347). Qed.
Lemma lem1994830 : term349 = term24.
Proof. exact (TRANS (@lem1994826) (@lem1994829)). Qed.
Lemma lem1994831 : term24 = term349.
Proof. exact (SYM (@lem1994830)). Qed.
Lemma lem1994832 : term365 = term349.
Proof. exact (TRANS (@lem1994814) (@lem1994831)). Qed.
Lemma lem1994834 : term366 = term62.
Proof. exact (@lem1994779 (@lem1994832)). Qed.
Lemma lem1994836 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1994837 : term62 = term24.
Proof. exact (@lem1994836 term24). Qed.
Lemma lem1994838 : term366 = term24.
Proof. exact (TRANS (@lem1994834) (@lem1994837)). Qed.
Lemma lem1994839 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1994840 : term367 = term126.
Proof. exact (MK_COMB (@lem1994839) (@lem1994838)). Qed.
Lemma lem1994841 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1994842 (y : real) : (term355 y) = (term131 y).
Proof. exact (MK_COMB (@lem1994840) (@lem1994841 y)). Qed.
Lemma lem1994843 (y : real) : (term354 y) = (term131 y).
Proof. exact (TRANS (@lem1994740 y) (@lem1994842 y)). Qed.
Lemma lem1994844 (y : real) : (term131 y) = term24.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1994845 (y : real) : (term354 y) = term24.
Proof. exact (TRANS (@lem1994843 y) (@lem1994844 y)). Qed.
Lemma lem1994846 (x : real) (y : real) : (term328 x y) = term149.
Proof. exact (MK_COMB (@lem1994739 x) (@lem1994845 y)). Qed.
Lemma lem1994847 (x : real) (y : real) : (term327 x y) = term149.
Proof. exact (TRANS (@lem1994631 x y) (@lem1994846 x y)). Qed.
Lemma lem1994848 : term149 = term24.
Proof. exact (@lem1982721 term24). Qed.
Lemma lem1994849 (x : real) (y : real) : (term327 x y) = term24.
Proof. exact (TRANS (@lem1994847 x y) (@lem1994848)). Qed.
Lemma lem1994850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1994851 (x : real) (y : real) : (term368 x y) = term151.
Proof. exact (MK_COMB (@lem1994850) (@lem1994849 x y)). Qed.
Lemma lem1994852 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994853 (x : real) (y : real) : (term326 x y) = term152.
Proof. exact (MK_COMB (@lem1994851 x y) (@lem1994852)). Qed.
Lemma lem1994854 (x : real) (y : real) (h1 : term304 x y) : term152.
Proof. exact (EQ_MP (@lem1994853 x y) (@lem1994630 x y h1)). Qed.
Lemma lem1994856 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1994857 : term152 = term153.
Proof. exact (@lem1994856 term24 term24). Qed.
Lemma lem1994859 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994860 : term24 = term62.
Proof. exact (@lem1994859 (NUMERAL 0)). Qed.
Lemma lem1994862 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994863 : term24 = term62.
Proof. exact (@lem1994862 (NUMERAL 0)). Qed.
Lemma lem1994864 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994865 : term63 = term64.
Proof. exact (MK_COMB (@lem1994864) (@lem1994863)). Qed.
Lemma lem1994866 : term153 = term154.
Proof. exact (MK_COMB (@lem1994865) (@lem1994860)). Qed.
Lemma lem1994867 : term155.
Proof. exact (@lem1980255 term24 term58 term24 term58). Qed.
Lemma lem1994869 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994870 : term57 = term68.
Proof. exact (@lem1994869 (NUMERAL 0) term61). Qed.
Lemma lem1994871 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994872 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994873 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994872 h1) (fun h1 : term68 = True => @lem1994871)). Qed.
Lemma lem1994874 : term68 = True.
Proof. exact (EQ_MP (@lem1994873) (@lem1994871)). Qed.
Lemma lem1994875 : term57 = True.
Proof. exact (TRANS (@lem1994870) (@lem1994874)). Qed.
Lemma lem1994876 : True = term57.
Proof. exact (SYM (@lem1994875)). Qed.
Lemma lem1994877 : term57.
Proof. exact (EQ_MP (@lem1994876) (@lem0)). Qed.
Lemma lem1994878 : term156.
Proof. exact (@lem1994867 (@lem1994877)). Qed.
Lemma lem1994880 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994881 : term57 = term68.
Proof. exact (@lem1994880 (NUMERAL 0) term61). Qed.
Lemma lem1994882 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994883 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994884 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994883 h1) (fun h1 : term68 = True => @lem1994882)). Qed.
Lemma lem1994885 : term68 = True.
Proof. exact (EQ_MP (@lem1994884) (@lem1994882)). Qed.
Lemma lem1994886 : term57 = True.
Proof. exact (TRANS (@lem1994881) (@lem1994885)). Qed.
Lemma lem1994887 : True = term57.
Proof. exact (SYM (@lem1994886)). Qed.
Lemma lem1994888 : term57.
Proof. exact (EQ_MP (@lem1994887) (@lem0)). Qed.
Lemma lem1994889 : term154 = term157.
Proof. exact (@lem1994878 (@lem1994888)). Qed.
Lemma lem1994891 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994892 : term79 = term24.
Proof. exact (@lem1994891 term61). Qed.
Lemma lem1994894 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994895 : term79 = term24.
Proof. exact (@lem1994894 term61). Qed.
Lemma lem1994896 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994897 : term80 = term63.
Proof. exact (MK_COMB (@lem1994896) (@lem1994895)). Qed.
Lemma lem1994898 : term157 = term153.
Proof. exact (MK_COMB (@lem1994897) (@lem1994892)). Qed.
Lemma lem1994900 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994901 : term153 = term158.
Proof. exact (@lem1994900 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1994902 : term158 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1994903 : term153 = False.
Proof. exact (TRANS (@lem1994901) (@lem1994902)). Qed.
Lemma lem1994904 : term157 = False.
Proof. exact (TRANS (@lem1994898) (@lem1994903)). Qed.
Lemma lem1994905 : term154 = False.
Proof. exact (TRANS (@lem1994889) (@lem1994904)). Qed.
Lemma lem1994906 : term153 = False.
Proof. exact (TRANS (@lem1994866) (@lem1994905)). Qed.
Lemma lem1994907 : term152 = False.
Proof. exact (TRANS (@lem1994857) (@lem1994906)). Qed.
Lemma lem1994908 (x : real) (y : real) (h1 : term304 x y) : False.
Proof. exact (EQ_MP (@lem1994907) (@lem1994854 x y h1)). Qed.
Lemma lem1994909 (x : real) (y : real) (h1 : term369 x y) : term369 x y.
Proof. exact (h1). Qed.
Lemma lem1994910 (x : real) (y : real) (h1 : term369 x y) : term136 x y.
Proof. exact (proj2 (@lem1994909 x y h1)). Qed.
Lemma lem1994911 (x : real) (y : real) (h1 : term369 x y) : term297 x y.
Proof. exact (proj1 (@lem1994909 x y h1)). Qed.
Lemma lem1994913 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1994914 : term56 = term57.
Proof. exact (@lem1994913 term24 term58). Qed.
Lemma lem1994916 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994917 : term58 = term60.
Proof. exact (@lem1994916 term61). Qed.
Lemma lem1994919 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994920 : term24 = term62.
Proof. exact (@lem1994919 (NUMERAL 0)). Qed.
Lemma lem1994921 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994922 : term63 = term64.
Proof. exact (MK_COMB (@lem1994921) (@lem1994920)). Qed.
Lemma lem1994923 : term57 = term65.
Proof. exact (MK_COMB (@lem1994922) (@lem1994917)). Qed.
Lemma lem1994924 : term66.
Proof. exact (@lem1980255 term24 term58 term58 term58). Qed.
Lemma lem1994926 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994927 : term57 = term68.
Proof. exact (@lem1994926 (NUMERAL 0) term61). Qed.
Lemma lem1994928 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994929 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994930 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994929 h1) (fun h1 : term68 = True => @lem1994928)). Qed.
Lemma lem1994931 : term68 = True.
Proof. exact (EQ_MP (@lem1994930) (@lem1994928)). Qed.
Lemma lem1994932 : term57 = True.
Proof. exact (TRANS (@lem1994927) (@lem1994931)). Qed.
Lemma lem1994933 : True = term57.
Proof. exact (SYM (@lem1994932)). Qed.
Lemma lem1994934 : term57.
Proof. exact (EQ_MP (@lem1994933) (@lem0)). Qed.
Lemma lem1994935 : term70.
Proof. exact (@lem1994924 (@lem1994934)). Qed.
Lemma lem1994937 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994938 : term57 = term68.
Proof. exact (@lem1994937 (NUMERAL 0) term61). Qed.
Lemma lem1994939 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994940 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994941 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994940 h1) (fun h1 : term68 = True => @lem1994939)). Qed.
Lemma lem1994942 : term68 = True.
Proof. exact (EQ_MP (@lem1994941) (@lem1994939)). Qed.
Lemma lem1994943 : term57 = True.
Proof. exact (TRANS (@lem1994938) (@lem1994942)). Qed.
Lemma lem1994944 : True = term57.
Proof. exact (SYM (@lem1994943)). Qed.
Lemma lem1994945 : term57.
Proof. exact (EQ_MP (@lem1994944) (@lem0)). Qed.
Lemma lem1994946 : term65 = term71.
Proof. exact (@lem1994935 (@lem1994945)). Qed.
Lemma lem1994948 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1994949 : term74 = term75.
Proof. exact (@lem1994948 term61 term61). Qed.
Lemma lem1994950 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1994951 : term77 = term61.
Proof. exact (EQ_MP (@lem1994950) (@lem940073)). Qed.
Lemma lem1994952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1994953 : term75 = term58.
Proof. exact (MK_COMB (@lem1994952) (@lem1994951)). Qed.
Lemma lem1994954 : term74 = term58.
Proof. exact (TRANS (@lem1994949) (@lem1994953)). Qed.
Lemma lem1994956 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1994957 : term79 = term24.
Proof. exact (@lem1994956 term61). Qed.
Lemma lem1994958 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994959 : term80 = term63.
Proof. exact (MK_COMB (@lem1994958) (@lem1994957)). Qed.
Lemma lem1994960 : term71 = term57.
Proof. exact (MK_COMB (@lem1994959) (@lem1994954)). Qed.
Lemma lem1994962 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994963 : term57 = term68.
Proof. exact (@lem1994962 (NUMERAL 0) term61). Qed.
Lemma lem1994964 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1994965 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1994966 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1994965 h1) (fun h1 : term68 = True => @lem1994964)). Qed.
Lemma lem1994967 : term68 = True.
Proof. exact (EQ_MP (@lem1994966) (@lem1994964)). Qed.
Lemma lem1994968 : term57 = True.
Proof. exact (TRANS (@lem1994963) (@lem1994967)). Qed.
Lemma lem1994969 : term71 = True.
Proof. exact (TRANS (@lem1994960) (@lem1994968)). Qed.
Lemma lem1994970 : term65 = True.
Proof. exact (TRANS (@lem1994946) (@lem1994969)). Qed.
Lemma lem1994971 : term57 = True.
Proof. exact (TRANS (@lem1994923) (@lem1994970)). Qed.
Lemma lem1994972 : term56 = True.
Proof. exact (TRANS (@lem1994914) (@lem1994971)). Qed.
Lemma lem1994973 : True = term56.
Proof. exact (SYM (@lem1994972)). Qed.
Lemma lem1994974 : term56.
Proof. exact (EQ_MP (@lem1994973) (@lem0)). Qed.
Lemma lem1994975 (x : real) (y : real) (h1 : term369 x y) : term370 x y.
Proof. exact (conj (@lem1994974) (@lem1994911 x y h1)). Qed.
Lemma lem1994977 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1994978 (x : real) (y : real) : term371 x y.
Proof. exact (@lem1994977 term58 (term261 x y)). Qed.
Lemma lem1994979 (x : real) (y : real) (h1 : term369 x y) : term372 x y.
Proof. exact (@lem1994978 x y (@lem1994975 x y h1)). Qed.
Lemma lem1994980 (x : real) (y : real) : (term308 x y) = (term261 x y).
Proof. exact (@lem1982733 (term261 x y)). Qed.
Lemma lem1994981 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1994982 (x : real) (y : real) : (term373 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1994981) (@lem1994980 x y)). Qed.
Lemma lem1994983 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1994984 (x : real) (y : real) : (term372 x y) = (term297 x y).
Proof. exact (MK_COMB (@lem1994982 x y) (@lem1994983)). Qed.
Lemma lem1994985 (x : real) (y : real) (h1 : term369 x y) : term297 x y.
Proof. exact (EQ_MP (@lem1994984 x y) (@lem1994979 x y h1)). Qed.
Lemma lem1994987 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1994988 : term310 = term311.
Proof. exact (@lem1994987 term24 term183). Qed.
Lemma lem1994989 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1994991 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1994992 : term24 = term62.
Proof. exact (@lem1994991 (NUMERAL 0)). Qed.
Lemma lem1994993 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1994994 : term63 = term64.
Proof. exact (MK_COMB (@lem1994993) (@lem1994992)). Qed.
Lemma lem1994995 : term311 = term312.
Proof. exact (MK_COMB (@lem1994994) (@lem1994989)). Qed.
Lemma lem1994996 : term313.
Proof. exact (@lem1980255 term24 term179 term58 term58). Qed.
Lemma lem1994998 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1994999 : term57 = term68.
Proof. exact (@lem1994998 (NUMERAL 0) term61). Qed.
Lemma lem1995000 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1995001 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1995002 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1995001 h1) (fun h1 : term68 = True => @lem1995000)). Qed.
Lemma lem1995003 : term68 = True.
Proof. exact (EQ_MP (@lem1995002) (@lem1995000)). Qed.
Lemma lem1995004 : term57 = True.
Proof. exact (TRANS (@lem1994999) (@lem1995003)). Qed.
Lemma lem1995005 : True = term57.
Proof. exact (SYM (@lem1995004)). Qed.
Lemma lem1995006 : term57.
Proof. exact (EQ_MP (@lem1995005) (@lem0)). Qed.
Lemma lem1995007 : term314.
Proof. exact (@lem1994996 (@lem1995006)). Qed.
Lemma lem1995009 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995010 : term220 = term221.
Proof. exact (@lem1995009 (NUMERAL 0) term184). Qed.
Lemma lem1995011 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1995012 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1995013 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1995012 h1) (fun h1 : term221 = True => @lem1995011)). Qed.
Lemma lem1995014 : term221 = True.
Proof. exact (EQ_MP (@lem1995013) (@lem1995011)). Qed.
Lemma lem1995015 : term220 = True.
Proof. exact (TRANS (@lem1995010) (@lem1995014)). Qed.
Lemma lem1995016 : True = term220.
Proof. exact (SYM (@lem1995015)). Qed.
Lemma lem1995017 : term220.
Proof. exact (EQ_MP (@lem1995016) (@lem0)). Qed.
Lemma lem1995018 : term312 = term315.
Proof. exact (@lem1995007 (@lem1995017)). Qed.
Lemma lem1995020 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1995021 : term74 = term75.
Proof. exact (@lem1995020 term61 term61). Qed.
Lemma lem1995022 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1995023 : term77 = term61.
Proof. exact (EQ_MP (@lem1995022) (@lem940073)). Qed.
Lemma lem1995024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995025 : term75 = term58.
Proof. exact (MK_COMB (@lem1995024) (@lem1995023)). Qed.
Lemma lem1995026 : term74 = term58.
Proof. exact (TRANS (@lem1995021) (@lem1995025)). Qed.
Lemma lem1995028 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995029 : term316 = term24.
Proof. exact (@lem1995028 term184). Qed.
Lemma lem1995030 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1995031 : term317 = term63.
Proof. exact (MK_COMB (@lem1995030) (@lem1995029)). Qed.
Lemma lem1995032 : term315 = term57.
Proof. exact (MK_COMB (@lem1995031) (@lem1995026)). Qed.
Lemma lem1995034 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995035 : term57 = term68.
Proof. exact (@lem1995034 (NUMERAL 0) term61). Qed.
Lemma lem1995036 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1995037 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1995038 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1995037 h1) (fun h1 : term68 = True => @lem1995036)). Qed.
Lemma lem1995039 : term68 = True.
Proof. exact (EQ_MP (@lem1995038) (@lem1995036)). Qed.
Lemma lem1995040 : term57 = True.
Proof. exact (TRANS (@lem1995035) (@lem1995039)). Qed.
Lemma lem1995041 : term315 = True.
Proof. exact (TRANS (@lem1995032) (@lem1995040)). Qed.
Lemma lem1995042 : term312 = True.
Proof. exact (TRANS (@lem1995018) (@lem1995041)). Qed.
Lemma lem1995043 : term311 = True.
Proof. exact (TRANS (@lem1994995) (@lem1995042)). Qed.
Lemma lem1995044 : term310 = True.
Proof. exact (TRANS (@lem1994988) (@lem1995043)). Qed.
Lemma lem1995045 : True = term310.
Proof. exact (SYM (@lem1995044)). Qed.
Lemma lem1995046 : term310.
Proof. exact (EQ_MP (@lem1995045) (@lem0)). Qed.
Lemma lem1995047 (x : real) (y : real) (h1 : term369 x y) : term318 x y.
Proof. exact (conj (@lem1995046) (@lem1994910 x y h1)). Qed.
Lemma lem1995049 (x : real) (y : real) : term93 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1995050 (x : real) (y : real) : term319 x y.
Proof. exact (@lem1995049 term183 (term19 x y)). Qed.
Lemma lem1995051 (x : real) (y : real) (h1 : term369 x y) : term320 x y.
Proof. exact (@lem1995050 x y (@lem1995047 x y h1)). Qed.
Lemma lem1995052 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1982781 x term183 (term21 y)). Qed.
Lemma lem1995053 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem1982749 term183 term106 y). Qed.
Lemma lem1995055 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1995056 : term106 = term109.
Proof. exact (@lem1995055 term61). Qed.
Lemma lem1995059 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1995060 : term193 = term194.
Proof. exact (MK_COMB (@lem1995059) (@lem1995056)). Qed.
Lemma lem1995061 : term194 = term195.
Proof. exact (@lem1981613 term58 term106 term179 term58). Qed.
Lemma lem1995063 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1995064 : term196 = term197.
Proof. exact (@lem1995063 term184 term61). Qed.
Lemma lem1995065 : term198 = term199.
Proof. exact (@lem996237 term199). Qed.
Lemma lem1995066 : (term198 = term199) = (term200 = term184).
Proof. exact (@lem1007663 term199 (BIT1 0) term199). Qed.
Lemma lem1995067 : term200 = term184.
Proof. exact (EQ_MP (@lem1995066) (@lem1995065)). Qed.
Lemma lem1995068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995069 : term197 = term179.
Proof. exact (MK_COMB (@lem1995068) (@lem1995067)). Qed.
Lemma lem1995070 : term196 = term179.
Proof. exact (TRANS (@lem1995064) (@lem1995069)). Qed.
Lemma lem1995072 (m : nat) (n : nat) : (term201 m n) = (term119 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1995073 : term202 = term121.
Proof. exact (@lem1995072 term61 term61). Qed.
Lemma lem1995074 : (term76 = (BIT1 0)) = (term77 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1995075 : term77 = term61.
Proof. exact (EQ_MP (@lem1995074) (@lem940073)). Qed.
Lemma lem1995076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995077 : term75 = term58.
Proof. exact (MK_COMB (@lem1995076) (@lem1995075)). Qed.
Lemma lem1995078 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1995079 : term121 = term106.
Proof. exact (MK_COMB (@lem1995078) (@lem1995077)). Qed.
Lemma lem1995080 : term202 = term106.
Proof. exact (TRANS (@lem1995073) (@lem1995079)). Qed.
Lemma lem1995081 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1995082 : term203 = term204.
Proof. exact (MK_COMB (@lem1995081) (@lem1995080)). Qed.
Lemma lem1995083 : term195 = term205.
Proof. exact (MK_COMB (@lem1995082) (@lem1995070)). Qed.
Lemma lem1995084 : term194 = term205.
Proof. exact (TRANS (@lem1995061) (@lem1995083)). Qed.
Lemma lem1995087 : term193 = term205.
Proof. exact (TRANS (@lem1995060) (@lem1995084)). Qed.
Lemma lem1995088 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1995089 : term206 = term207.
Proof. exact (MK_COMB (@lem1995088) (@lem1995087)). Qed.
Lemma lem1995090 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1995091 (y : real) : (term191 y) = (term208 y).
Proof. exact (MK_COMB (@lem1995089) (@lem1995090 y)). Qed.
Lemma lem1995092 (y : real) : (term190 y) = (term208 y).
Proof. exact (TRANS (@lem1995053 y) (@lem1995091 y)). Qed.
Lemma lem1995095 (x : real) : (term209 x) = (term209 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1995096 (x : real) (y : real) : (term189 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1995095 x) (@lem1995092 y)). Qed.
Lemma lem1995097 (x : real) (y : real) : (term188 x y) = (term210 x y).
Proof. exact (TRANS (@lem1995052 x y) (@lem1995096 x y)). Qed.
Lemma lem1995098 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1995099 (x : real) (y : real) : (term321 x y) = (term322 x y).
Proof. exact (MK_COMB (@lem1995098) (@lem1995097 x y)). Qed.
Lemma lem1995100 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1995101 (x : real) (y : real) : (term320 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1995099 x y) (@lem1995100)). Qed.
Lemma lem1995102 (x : real) (y : real) (h1 : term369 x y) : term323 x y.
Proof. exact (EQ_MP (@lem1995101 x y) (@lem1995051 x y h1)). Qed.
Lemma lem1995103 (x : real) (y : real) (h1 : term369 x y) : term374 x y.
Proof. exact (conj (@lem1995102 x y h1) (@lem1994985 x y h1)). Qed.
Lemma lem1995105 (x : real) (y : real) : term375 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem1995106 (x : real) (y : real) : term376 x y.
Proof. exact (@lem1995105 (term210 x y) (term261 x y)). Qed.
Lemma lem1995107 (x : real) (y : real) (h1 : term369 x y) : term326 x y.
Proof. exact (@lem1995106 x y (@lem1995103 x y h1)). Qed.
Lemma lem1995108 (x : real) (y : real) : (term327 x y) = (term328 x y).
Proof. exact (@lem1982753 (term213 x) (term208 x) (term208 y) (term213 y)). Qed.
Lemma lem1995109 (x : real) : (term329 x) = (term330 x).
Proof. exact (@lem1982711 term183 term205 x). Qed.
Lemma lem1995115 : term331.
Proof. exact (@lem1981473 term58 term179 term106 term179 term24 term58). Qed.
Lemma lem1995117 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995118 : term220 = term221.
Proof. exact (@lem1995117 (NUMERAL 0) term184). Qed.
Lemma lem1995119 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1995120 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1995121 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1995120 h1) (fun h1 : term221 = True => @lem1995119)). Qed.
Lemma lem1995122 : term221 = True.
Proof. exact (EQ_MP (@lem1995121) (@lem1995119)). Qed.
Lemma lem1995123 : term220 = True.
Proof. exact (TRANS (@lem1995118) (@lem1995122)). Qed.
Lemma lem1995124 : True = term220.
Proof. exact (SYM (@lem1995123)). Qed.
Lemma lem1995125 : term220.
Proof. exact (EQ_MP (@lem1995124) (@lem0)). Qed.
Lemma lem1995126 : term332.
Proof. exact (@lem1995115 (@lem1995125)). Qed.
Lemma lem1995128 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995129 : term220 = term221.
Proof. exact (@lem1995128 (NUMERAL 0) term184). Qed.
Lemma lem1995130 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1995131 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1995132 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1995131 h1) (fun h1 : term221 = True => @lem1995130)). Qed.
Lemma lem1995133 : term221 = True.
Proof. exact (EQ_MP (@lem1995132) (@lem1995130)). Qed.
Lemma lem1995134 : term220 = True.
Proof. exact (TRANS (@lem1995129) (@lem1995133)). Qed.
Lemma lem1995135 : True = term220.
Proof. exact (SYM (@lem1995134)). Qed.
Lemma lem1995136 : term220.
Proof. exact (EQ_MP (@lem1995135) (@lem0)). Qed.
Lemma lem1995137 : term333.
Proof. exact (@lem1995126 (@lem1995136)). Qed.
Lemma lem1995139 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995140 : term57 = term68.
Proof. exact (@lem1995139 (NUMERAL 0) term61). Qed.
Lemma lem1995141 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1995142 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1995143 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1995142 h1) (fun h1 : term68 = True => @lem1995141)). Qed.
Lemma lem1995144 : term68 = True.
Proof. exact (EQ_MP (@lem1995143) (@lem1995141)). Qed.
Lemma lem1995145 : term57 = True.
Proof. exact (TRANS (@lem1995140) (@lem1995144)). Qed.
Lemma lem1995146 : True = term57.
Proof. exact (SYM (@lem1995145)). Qed.
Lemma lem1995147 : term57.
Proof. exact (EQ_MP (@lem1995146) (@lem0)). Qed.
Lemma lem1995148 : term334.
Proof. exact (@lem1995137 (@lem1995147)). Qed.
Lemma lem1995150 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1995151 : term281 = term282.
Proof. exact (@lem1995150 term61 term184). Qed.
Lemma lem1995152 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1995153 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1995154 : term229 = term184.
Proof. exact (EQ_MP (@lem1995153) (@lem1995152)). Qed.
Lemma lem1995155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995156 : term227 = term179.
Proof. exact (MK_COMB (@lem1995155) (@lem1995154)). Qed.
Lemma lem1995157 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1995158 : term282 = term283.
Proof. exact (MK_COMB (@lem1995157) (@lem1995156)). Qed.
Lemma lem1995159 : term281 = term283.
Proof. exact (TRANS (@lem1995151) (@lem1995158)). Qed.
Lemma lem1995161 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1995162 : term226 = term227.
Proof. exact (@lem1995161 term61 term184). Qed.
Lemma lem1995163 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1995164 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1995165 : term229 = term184.
Proof. exact (EQ_MP (@lem1995164) (@lem1995163)). Qed.
Lemma lem1995166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995167 : term227 = term179.
Proof. exact (MK_COMB (@lem1995166) (@lem1995165)). Qed.
Lemma lem1995168 : term226 = term179.
Proof. exact (TRANS (@lem1995162) (@lem1995167)). Qed.
Lemma lem1995169 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1995170 : term335 = term336.
Proof. exact (MK_COMB (@lem1995169) (@lem1995168)). Qed.
Lemma lem1995171 : term337 = term338.
Proof. exact (MK_COMB (@lem1995170) (@lem1995159)). Qed.
Lemma lem1995173 (m : nat) : (term339 m) = term24.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1995174 : term338 = term24.
Proof. exact (@lem1995173 term184). Qed.
Lemma lem1995175 : term337 = term24.
Proof. exact (TRANS (@lem1995171) (@lem1995174)). Qed.
Lemma lem1995176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1995177 : term340 = term126.
Proof. exact (MK_COMB (@lem1995176) (@lem1995175)). Qed.
Lemma lem1995178 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1995179 : term341 = term79.
Proof. exact (MK_COMB (@lem1995177) (@lem1995178)). Qed.
Lemma lem1995181 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995182 : term79 = term24.
Proof. exact (@lem1995181 term61). Qed.
Lemma lem1995183 : term341 = term24.
Proof. exact (TRANS (@lem1995179) (@lem1995182)). Qed.
Lemma lem1995185 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1995186 : term342 = term343.
Proof. exact (@lem1995185 term184 term184). Qed.
Lemma lem1995187 : (term76 = (BIT1 0)) = (term344 = term345).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1995188 : term344 = term345.
Proof. exact (EQ_MP (@lem1995187) (@lem940073)). Qed.
Lemma lem1995189 : (term344 = term345) = (term346 = term347).
Proof. exact (@lem1008952 term199 term345). Qed.
Lemma lem1995190 : term346 = term347.
Proof. exact (EQ_MP (@lem1995189) (@lem1995188)). Qed.
Lemma lem1995191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995192 : term343 = term348.
Proof. exact (MK_COMB (@lem1995191) (@lem1995190)). Qed.
Lemma lem1995193 : term342 = term348.
Proof. exact (TRANS (@lem1995186) (@lem1995192)). Qed.
Lemma lem1995194 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1995195 : term349 = term350.
Proof. exact (MK_COMB (@lem1995194) (@lem1995193)). Qed.
Lemma lem1995197 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995198 : term350 = term24.
Proof. exact (@lem1995197 term347). Qed.
Lemma lem1995199 : term349 = term24.
Proof. exact (TRANS (@lem1995195) (@lem1995198)). Qed.
Lemma lem1995200 : term24 = term349.
Proof. exact (SYM (@lem1995199)). Qed.
Lemma lem1995201 : term341 = term349.
Proof. exact (TRANS (@lem1995183) (@lem1995200)). Qed.
Lemma lem1995203 : term351 = term62.
Proof. exact (@lem1995148 (@lem1995201)). Qed.
Lemma lem1995205 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1995206 : term62 = term24.
Proof. exact (@lem1995205 term24). Qed.
Lemma lem1995207 : term351 = term24.
Proof. exact (TRANS (@lem1995203) (@lem1995206)). Qed.
Lemma lem1995208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1995209 : term352 = term126.
Proof. exact (MK_COMB (@lem1995208) (@lem1995207)). Qed.
Lemma lem1995210 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1995211 (x : real) : (term330 x) = (term131 x).
Proof. exact (MK_COMB (@lem1995209) (@lem1995210 x)). Qed.
Lemma lem1995212 (x : real) : (term329 x) = (term131 x).
Proof. exact (TRANS (@lem1995109 x) (@lem1995211 x)). Qed.
Lemma lem1995213 (x : real) : (term131 x) = term24.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1995214 (x : real) : (term329 x) = term24.
Proof. exact (TRANS (@lem1995212 x) (@lem1995213 x)). Qed.
Lemma lem1995215 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1995216 (x : real) : (term353 x) = term147.
Proof. exact (MK_COMB (@lem1995215) (@lem1995214 x)). Qed.
Lemma lem1995217 (y : real) : (term354 y) = (term355 y).
Proof. exact (@lem1982711 term205 term183 y). Qed.
Lemma lem1995223 : term356.
Proof. exact (@lem1981473 term106 term179 term58 term179 term24 term58). Qed.
Lemma lem1995225 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995226 : term220 = term221.
Proof. exact (@lem1995225 (NUMERAL 0) term184). Qed.
Lemma lem1995227 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1995228 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1995229 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1995228 h1) (fun h1 : term221 = True => @lem1995227)). Qed.
Lemma lem1995230 : term221 = True.
Proof. exact (EQ_MP (@lem1995229) (@lem1995227)). Qed.
Lemma lem1995231 : term220 = True.
Proof. exact (TRANS (@lem1995226) (@lem1995230)). Qed.
Lemma lem1995232 : True = term220.
Proof. exact (SYM (@lem1995231)). Qed.
Lemma lem1995233 : term220.
Proof. exact (EQ_MP (@lem1995232) (@lem0)). Qed.
Lemma lem1995234 : term357.
Proof. exact (@lem1995223 (@lem1995233)). Qed.
Lemma lem1995236 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995237 : term220 = term221.
Proof. exact (@lem1995236 (NUMERAL 0) term184). Qed.
Lemma lem1995238 : term222 = term199.
Proof. exact (@lem912803). Qed.
Lemma lem1995239 (h1 : term222 = term199) : term221 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term199 h1). Qed.
Lemma lem1995240 : (term222 = term199) = (term221 = True).
Proof. exact (prop_ext (fun h1 : term222 = term199 => @lem1995239 h1) (fun h1 : term221 = True => @lem1995238)). Qed.
Lemma lem1995241 : term221 = True.
Proof. exact (EQ_MP (@lem1995240) (@lem1995238)). Qed.
Lemma lem1995242 : term220 = True.
Proof. exact (TRANS (@lem1995237) (@lem1995241)). Qed.
Lemma lem1995243 : True = term220.
Proof. exact (SYM (@lem1995242)). Qed.
Lemma lem1995244 : term220.
Proof. exact (EQ_MP (@lem1995243) (@lem0)). Qed.
Lemma lem1995245 : term358.
Proof. exact (@lem1995234 (@lem1995244)). Qed.
Lemma lem1995247 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995248 : term57 = term68.
Proof. exact (@lem1995247 (NUMERAL 0) term61). Qed.
Lemma lem1995249 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1995250 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1995251 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1995250 h1) (fun h1 : term68 = True => @lem1995249)). Qed.
Lemma lem1995252 : term68 = True.
Proof. exact (EQ_MP (@lem1995251) (@lem1995249)). Qed.
Lemma lem1995253 : term57 = True.
Proof. exact (TRANS (@lem1995248) (@lem1995252)). Qed.
Lemma lem1995254 : True = term57.
Proof. exact (SYM (@lem1995253)). Qed.
Lemma lem1995255 : term57.
Proof. exact (EQ_MP (@lem1995254) (@lem0)). Qed.
Lemma lem1995256 : term359.
Proof. exact (@lem1995245 (@lem1995255)). Qed.
Lemma lem1995258 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1995259 : term226 = term227.
Proof. exact (@lem1995258 term61 term184). Qed.
Lemma lem1995260 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1995261 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1995262 : term229 = term184.
Proof. exact (EQ_MP (@lem1995261) (@lem1995260)). Qed.
Lemma lem1995263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995264 : term227 = term179.
Proof. exact (MK_COMB (@lem1995263) (@lem1995262)). Qed.
Lemma lem1995265 : term226 = term179.
Proof. exact (TRANS (@lem1995259) (@lem1995264)). Qed.
Lemma lem1995267 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1995268 : term281 = term282.
Proof. exact (@lem1995267 term61 term184). Qed.
Lemma lem1995269 : term228 = term199.
Proof. exact (@lem996238 term199). Qed.
Lemma lem1995270 : (term228 = term199) = (term229 = term184).
Proof. exact (@lem1007663 (BIT1 0) term199 term199). Qed.
Lemma lem1995271 : term229 = term184.
Proof. exact (EQ_MP (@lem1995270) (@lem1995269)). Qed.
Lemma lem1995272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995273 : term227 = term179.
Proof. exact (MK_COMB (@lem1995272) (@lem1995271)). Qed.
Lemma lem1995274 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1995275 : term282 = term283.
Proof. exact (MK_COMB (@lem1995274) (@lem1995273)). Qed.
Lemma lem1995276 : term281 = term283.
Proof. exact (TRANS (@lem1995268) (@lem1995275)). Qed.
Lemma lem1995277 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1995278 : term360 = term361.
Proof. exact (MK_COMB (@lem1995277) (@lem1995276)). Qed.
Lemma lem1995279 : term362 = term363.
Proof. exact (MK_COMB (@lem1995278) (@lem1995265)). Qed.
Lemma lem1995281 (m : nat) : (term124 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1995282 : term363 = term24.
Proof. exact (@lem1995281 term184). Qed.
Lemma lem1995283 : term362 = term24.
Proof. exact (TRANS (@lem1995279) (@lem1995282)). Qed.
Lemma lem1995284 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1995285 : term364 = term126.
Proof. exact (MK_COMB (@lem1995284) (@lem1995283)). Qed.
Lemma lem1995286 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1995287 : term365 = term79.
Proof. exact (MK_COMB (@lem1995285) (@lem1995286)). Qed.
Lemma lem1995289 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995290 : term79 = term24.
Proof. exact (@lem1995289 term61). Qed.
Lemma lem1995291 : term365 = term24.
Proof. exact (TRANS (@lem1995287) (@lem1995290)). Qed.
Lemma lem1995293 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1995294 : term342 = term343.
Proof. exact (@lem1995293 term184 term184). Qed.
Lemma lem1995295 : (term76 = (BIT1 0)) = (term344 = term345).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1995296 : term344 = term345.
Proof. exact (EQ_MP (@lem1995295) (@lem940073)). Qed.
Lemma lem1995297 : (term344 = term345) = (term346 = term347).
Proof. exact (@lem1008952 term199 term345). Qed.
Lemma lem1995298 : term346 = term347.
Proof. exact (EQ_MP (@lem1995297) (@lem1995296)). Qed.
Lemma lem1995299 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1995300 : term343 = term348.
Proof. exact (MK_COMB (@lem1995299) (@lem1995298)). Qed.
Lemma lem1995301 : term342 = term348.
Proof. exact (TRANS (@lem1995294) (@lem1995300)). Qed.
Lemma lem1995302 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem1995303 : term349 = term350.
Proof. exact (MK_COMB (@lem1995302) (@lem1995301)). Qed.
Lemma lem1995305 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995306 : term350 = term24.
Proof. exact (@lem1995305 term347). Qed.
Lemma lem1995307 : term349 = term24.
Proof. exact (TRANS (@lem1995303) (@lem1995306)). Qed.
Lemma lem1995308 : term24 = term349.
Proof. exact (SYM (@lem1995307)). Qed.
Lemma lem1995309 : term365 = term349.
Proof. exact (TRANS (@lem1995291) (@lem1995308)). Qed.
Lemma lem1995311 : term366 = term62.
Proof. exact (@lem1995256 (@lem1995309)). Qed.
Lemma lem1995313 (x : real) : (term129 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1995314 : term62 = term24.
Proof. exact (@lem1995313 term24). Qed.
Lemma lem1995315 : term366 = term24.
Proof. exact (TRANS (@lem1995311) (@lem1995314)). Qed.
Lemma lem1995316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1995317 : term367 = term126.
Proof. exact (MK_COMB (@lem1995316) (@lem1995315)). Qed.
Lemma lem1995318 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1995319 (y : real) : (term355 y) = (term131 y).
Proof. exact (MK_COMB (@lem1995317) (@lem1995318 y)). Qed.
Lemma lem1995320 (y : real) : (term354 y) = (term131 y).
Proof. exact (TRANS (@lem1995217 y) (@lem1995319 y)). Qed.
Lemma lem1995321 (y : real) : (term131 y) = term24.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1995322 (y : real) : (term354 y) = term24.
Proof. exact (TRANS (@lem1995320 y) (@lem1995321 y)). Qed.
Lemma lem1995323 (x : real) (y : real) : (term328 x y) = term149.
Proof. exact (MK_COMB (@lem1995216 x) (@lem1995322 y)). Qed.
Lemma lem1995324 (x : real) (y : real) : (term327 x y) = term149.
Proof. exact (TRANS (@lem1995108 x y) (@lem1995323 x y)). Qed.
Lemma lem1995325 : term149 = term24.
Proof. exact (@lem1982721 term24). Qed.
Lemma lem1995326 (x : real) (y : real) : (term327 x y) = term24.
Proof. exact (TRANS (@lem1995324 x y) (@lem1995325)). Qed.
Lemma lem1995327 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1995328 (x : real) (y : real) : (term368 x y) = term151.
Proof. exact (MK_COMB (@lem1995327) (@lem1995326 x y)). Qed.
Lemma lem1995329 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1995330 (x : real) (y : real) : (term326 x y) = term152.
Proof. exact (MK_COMB (@lem1995328 x y) (@lem1995329)). Qed.
Lemma lem1995331 (x : real) (y : real) (h1 : term369 x y) : term152.
Proof. exact (EQ_MP (@lem1995330 x y) (@lem1995107 x y h1)). Qed.
Lemma lem1995333 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1995334 : term152 = term153.
Proof. exact (@lem1995333 term24 term24). Qed.
Lemma lem1995336 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1995337 : term24 = term62.
Proof. exact (@lem1995336 (NUMERAL 0)). Qed.
Lemma lem1995339 (x : nat) : (real_of_num x) = (term59 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1995340 : term24 = term62.
Proof. exact (@lem1995339 (NUMERAL 0)). Qed.
Lemma lem1995341 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1995342 : term63 = term64.
Proof. exact (MK_COMB (@lem1995341) (@lem1995340)). Qed.
Lemma lem1995343 : term153 = term154.
Proof. exact (MK_COMB (@lem1995342) (@lem1995337)). Qed.
Lemma lem1995344 : term155.
Proof. exact (@lem1980255 term24 term58 term24 term58). Qed.
Lemma lem1995346 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995347 : term57 = term68.
Proof. exact (@lem1995346 (NUMERAL 0) term61). Qed.
Lemma lem1995348 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1995349 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1995350 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1995349 h1) (fun h1 : term68 = True => @lem1995348)). Qed.
Lemma lem1995351 : term68 = True.
Proof. exact (EQ_MP (@lem1995350) (@lem1995348)). Qed.
Lemma lem1995352 : term57 = True.
Proof. exact (TRANS (@lem1995347) (@lem1995351)). Qed.
Lemma lem1995353 : True = term57.
Proof. exact (SYM (@lem1995352)). Qed.
Lemma lem1995354 : term57.
Proof. exact (EQ_MP (@lem1995353) (@lem0)). Qed.
Lemma lem1995355 : term156.
Proof. exact (@lem1995344 (@lem1995354)). Qed.
Lemma lem1995357 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995358 : term57 = term68.
Proof. exact (@lem1995357 (NUMERAL 0) term61). Qed.
Lemma lem1995359 : term69 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1995360 (h1 : term69 = (BIT1 0)) : term68 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1995361 : (term69 = (BIT1 0)) = (term68 = True).
Proof. exact (prop_ext (fun h1 : term69 = (BIT1 0) => @lem1995360 h1) (fun h1 : term68 = True => @lem1995359)). Qed.
Lemma lem1995362 : term68 = True.
Proof. exact (EQ_MP (@lem1995361) (@lem1995359)). Qed.
Lemma lem1995363 : term57 = True.
Proof. exact (TRANS (@lem1995358) (@lem1995362)). Qed.
Lemma lem1995364 : True = term57.
Proof. exact (SYM (@lem1995363)). Qed.
Lemma lem1995365 : term57.
Proof. exact (EQ_MP (@lem1995364) (@lem0)). Qed.
Lemma lem1995366 : term154 = term157.
Proof. exact (@lem1995355 (@lem1995365)). Qed.
Lemma lem1995368 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995369 : term79 = term24.
Proof. exact (@lem1995368 term61). Qed.
Lemma lem1995371 (x : nat) : (term78 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1995372 : term79 = term24.
Proof. exact (@lem1995371 term61). Qed.
Lemma lem1995373 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1995374 : term80 = term63.
Proof. exact (MK_COMB (@lem1995373) (@lem1995372)). Qed.
Lemma lem1995375 : term157 = term153.
Proof. exact (MK_COMB (@lem1995374) (@lem1995369)). Qed.
Lemma lem1995377 (m : nat) (n : nat) : (term67 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1995378 : term153 = term158.
Proof. exact (@lem1995377 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1995379 : term158 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1995380 : term153 = False.
Proof. exact (TRANS (@lem1995378) (@lem1995379)). Qed.
Lemma lem1995381 : term157 = False.
Proof. exact (TRANS (@lem1995375) (@lem1995380)). Qed.
Lemma lem1995382 : term154 = False.
Proof. exact (TRANS (@lem1995366) (@lem1995381)). Qed.
Lemma lem1995383 : term153 = False.
Proof. exact (TRANS (@lem1995343) (@lem1995382)). Qed.
Lemma lem1995384 : term152 = False.
Proof. exact (TRANS (@lem1995334) (@lem1995383)). Qed.
Lemma lem1995385 (x : real) (y : real) (h1 : term369 x y) : False.
Proof. exact (EQ_MP (@lem1995384) (@lem1995331 x y h1)). Qed.
Lemma lem1995386 (x : real) (y : real) (h1 : term303 x y) : False.
Proof. exact (or_elim (@lem1994431 x y h1) (fun h0 : term304 x y => @lem1994908 x y h0) (fun h0 : term369 x y => @lem1995385 x y h0)). Qed.
Lemma lem1995388 (x : real) (y : real) (h1 : term303 x y) : term303 x y.
Proof. exact (h1). Qed.
Lemma lem1995389 (x : real) (y : real) (h1 : term303 x y) : (term303 x y) = False.
Proof. exact (prop_ext (fun h2 : term303 x y => @lem1995386 x y h1) (fun h2 : False => @lem1995388 x y h1)). Qed.
Lemma lem1995390 (x : real) (y : real) (h1 : term303 x y) : False.
Proof. exact (EQ_MP (@lem1995389 x y h1) (@lem1995388 x y h1)). Qed.
Lemma lem1995391 (x : real) (y : real) (h1 : term173 x y) : term173 x y.
Proof. exact (h1). Qed.
Lemma lem1995392 (x : real) (y : real) (h1 : term173 x y) : term303 x y.
Proof. exact (EQ_MP (@lem1994421 x y) (@lem1995391 x y h1)). Qed.
Lemma lem1995393 (x : real) (y : real) (h1 : term173 x y) : (term303 x y) = False.
Proof. exact (prop_ext (fun h2 : term303 x y => @lem1995390 x y h2) (fun h2 : False => @lem1995392 x y h1)). Qed.
Lemma lem1995394 (x : real) (y : real) (h1 : term173 x y) : False.
Proof. exact (EQ_MP (@lem1995393 x y h1) (@lem1995392 x y h1)). Qed.
Lemma lem1995395 (x : real) (y : real) : term377 x y.
Proof. exact (fun h0 : term173 x y => @lem1995394 x y h0). Qed.
Lemma lem1995396 (x : real) (y : real) : term378 x y.
Proof. exact (@lem1386578 (term379 x y)). Qed.
Lemma lem1995399 (x : real) (y : real) : term379 x y.
Proof. exact (@lem1995396 x y (@lem1995395 x y)). Qed.
Lemma lem1995400 (y : real) (x : real) (h1 : term17 y x) : real_le x y.
Proof. exact (@lem1995399 x y (@lem1993539 y x h1)). Qed.
Lemma lem1995401 (x : real) (y : real) : term380 x y.
Proof. exact (fun h0 : term17 y x => @lem1995400 y x h0). Qed.
Lemma lem1995402 (x : real) (y : real) : term381 x y.
Proof. exact (conj (@lem1993535 y x) (@lem1995401 x y)). Qed.
Lemma lem1995403 (y : real) (x : real) : (term381 x y) = ((real_le x y) = (term17 y x)).
Proof. exact (@lem32 (real_le x y) (term17 y x)). Qed.
Lemma lem1995404 (y : real) (x : real) : (real_le x y) = (term17 y x).
Proof. exact (EQ_MP (@lem1995403 y x) (@lem1995402 x y)). Qed.
Lemma lem1995409 (x : real) : term382 x.
Proof. exact (fun y : real => @lem1995404 y x). Qed.
Lemma lem1995414 : term383.
Proof. exact (fun x : real => @lem1995409 x). Qed.
