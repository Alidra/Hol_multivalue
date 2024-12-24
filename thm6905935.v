Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6905935_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_MUL_LID_spec.
Require Import INT_MUL_RID_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm69_spec.
Require Import thm6904609_spec.
Require Import thm6904610_spec.
Lemma lem6904639 {A : Type'} (P : A -> Prop) (x : A) : term0 A P x.
Proof. exact (EQ_MP (@lem6904610 A P x) (@lem6904609 A P x)). Qed.
Lemma lem6904640 (P : int -> Prop) (x : int) : term1 P x.
Proof. exact (@lem6904639 int P x). Qed.
Lemma lem6904641 : term2.
Proof. exact (@lem6904640 term3 term4). Qed.
Lemma lem6904643 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6904644 : term6 = term7.
Proof. exact (@lem6904643 term6). Qed.
Lemma lem6904645 : term7 = term6.
Proof. exact (SYM (@lem6904644)). Qed.
Lemma lem6904646 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem6904649 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6904650 : term10.
Proof. exact (fun h0 : term9 => @lem6904649 h0). Qed.
Lemma lem6904651 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem6904652 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6904653 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem6904651 h2 (@lem6904652 h1)). Qed.
Lemma lem6904654 (h1 : term9) : term11.
Proof. exact (fun h0 : term10 => @lem6904653 h1 h0). Qed.
Lemma lem6904655 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem6904656 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem6904654 h1 (@lem6904655 h2)). Qed.
Lemma lem6904657 (h1 : term10) : term10.
Proof. exact (fun h0 : term9 => @lem6904656 h0 h1). Qed.
Lemma lem6904658 : term12.
Proof. exact (fun h0 : term10 => @lem6904657 h0). Qed.
Lemma lem6904661 : term10.
Proof. exact (@lem6904658 (@lem6904650)). Qed.
Lemma lem6904669 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem6904670 (P : int -> Prop) (Q : int -> Prop) : (term15 P Q) = (term16 P Q).
Proof. exact (@lem6904669 int P Q). Qed.
Lemma lem6904671 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem6904670 (term19 x) (term20 x)). Qed.
Lemma lem6904672 (x : int) (y : int) : (term21 x y) = ((int_mul x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem6904673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6904674 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem6904673) (@lem6904672 x y)). Qed.
Lemma lem6904675 (x : int) (y : int) : (term24 x y) = ((int_mul y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem6904676 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem6904674 x y) (@lem6904675 x y)). Qed.
Lemma lem6904677 (x : int) : (term27 x) = (term28 x).
Proof. exact (fun_ext (fun y : int => @lem6904676 x y)). Qed.
Lemma lem6904678 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904679 (x : int) : (term17 x) = (term29 x).
Proof. exact (MK_COMB (@lem6904678) (@lem6904677 x)). Qed.
Lemma lem6904680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6904681 (x : int) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem6904680) (@lem6904679 x)). Qed.
Lemma lem6904682 (x : int) (y : int) : (term21 x y) = ((int_mul x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem6904683 (x : int) : (term32 x) = (term19 x).
Proof. exact (fun_ext (fun y : int => @lem6904682 x y)). Qed.
Lemma lem6904684 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904685 (x : int) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem6904684) (@lem6904683 x)). Qed.
Lemma lem6904686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6904687 (x : int) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem6904686) (@lem6904685 x)). Qed.
Lemma lem6904688 (x : int) (y : int) : (term24 x y) = ((int_mul y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem6904689 (x : int) : (term37 x) = (term20 x).
Proof. exact (fun_ext (fun y : int => @lem6904688 x y)). Qed.
Lemma lem6904690 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904691 (x : int) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem6904690) (@lem6904689 x)). Qed.
Lemma lem6904692 (x : int) : (term18 x) = (term40 x).
Proof. exact (MK_COMB (@lem6904687 x) (@lem6904691 x)). Qed.
Lemma lem6904693 (x : int) : ((term17 x) = (term18 x)) = ((term29 x) = (term40 x)).
Proof. exact (MK_COMB (@lem6904681 x) (@lem6904692 x)). Qed.
Lemma lem6904694 (x : int) : (term29 x) = (term40 x).
Proof. exact (EQ_MP (@lem6904693 x) (@lem6904671 x)). Qed.
Lemma lem6904705 : term3 = term41.
Proof. exact (fun_ext (fun x : int => @lem6904694 x)). Qed.
Lemma lem6904706 (y : int) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6904707 (y : int) : (term42 y) = (term43 y).
Proof. exact (MK_COMB (@lem6904705) (@lem6904706 y)). Qed.
Lemma lem6904708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6904709 (y : int) : (term44 y) = (term45 y).
Proof. exact (MK_COMB (@lem6904708) (@lem6904707 y)). Qed.
Lemma lem6904710 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6904711 (y : int) : ((term42 y) = (y = term4)) = ((term43 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6904709 y) (@lem6904710 y)). Qed.
Lemma lem6904712 : term46 = term47.
Proof. exact (fun_ext (fun y : int => @lem6904711 y)). Qed.
Lemma lem6904713 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904714 : term6 = term48.
Proof. exact (MK_COMB (@lem6904713) (@lem6904712)). Qed.
Lemma lem6904719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904720 : term8 = term49.
Proof. exact (MK_COMB (@lem6904719) (@lem6904714)). Qed.
Lemma lem6904721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6904722 : term50 = term51.
Proof. exact (MK_COMB (@lem6904721) (@lem6904720)). Qed.
Lemma lem6904730 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6904731 : term52 = term53.
Proof. exact (@lem6904730 term54). Qed.
Lemma lem6904736 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem6904737 : term56 = term57.
Proof. exact (MK_COMB (@lem6904736) (@lem6904731)). Qed.
Lemma lem6904740 : term9 = term58.
Proof. exact (MK_COMB (@lem6904722) (@lem6904737)). Qed.
Lemma lem6904743 (y : int) : (term43 y) = (term40 y).
Proof. exact (eq_refl (term43 y)). Qed.
Lemma lem6904744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6904745 (y : int) : (term45 y) = (term59 y).
Proof. exact (MK_COMB (@lem6904744) (@lem6904743 y)). Qed.
Lemma lem6904746 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6904747 (y : int) : ((term43 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6904745 y) (@lem6904746 y)). Qed.
Lemma lem6904748 : term47 = term60.
Proof. exact (fun_ext (fun y : int => @lem6904747 y)). Qed.
Lemma lem6904749 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904750 : term48 = term61.
Proof. exact (MK_COMB (@lem6904749) (@lem6904748)). Qed.
Lemma lem6904751 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904752 : term49 = term62.
Proof. exact (MK_COMB (@lem6904751) (@lem6904750)). Qed.
Lemma lem6904753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6904754 : term51 = term63.
Proof. exact (MK_COMB (@lem6904753) (@lem6904752)). Qed.
Lemma lem6904755 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem6904756 : term58 = term64.
Proof. exact (MK_COMB (@lem6904754) (@lem6904755)). Qed.
Lemma lem6904759 : term9 = term64.
Proof. exact (TRANS (@lem6904740) (@lem6904756)). Qed.
Lemma lem6904760 (x : int) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6904761 : term66 = term66.
Proof. exact (fun_ext (fun x : int => @lem6904760 x)). Qed.
Lemma lem6904762 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904763 : term54 = term54.
Proof. exact (MK_COMB (@lem6904762) (@lem6904761)). Qed.
Lemma lem6904764 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904765 : term53 = term53.
Proof. exact (MK_COMB (@lem6904764) (@lem6904763)). Qed.
Lemma lem6904766 (x : int) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6904767 : term68 = term68.
Proof. exact (fun_ext (fun x : int => @lem6904766 x)). Qed.
Lemma lem6904768 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904769 : term69 = term69.
Proof. exact (MK_COMB (@lem6904768) (@lem6904767)). Qed.
Lemma lem6904770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6904771 : term55 = term55.
Proof. exact (MK_COMB (@lem6904770) (@lem6904769)). Qed.
Lemma lem6904772 : term57 = term57.
Proof. exact (MK_COMB (@lem6904771) (@lem6904765)). Qed.
Lemma lem6904773 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6904774 (y : int) (y' : int) : ((int_mul y' y) = y') = ((int_mul y' y) = y').
Proof. exact (eq_refl ((int_mul y' y) = y')). Qed.
Lemma lem6904775 (y : int) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : int => @lem6904774 y y')). Qed.
Lemma lem6904776 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904777 (y : int) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6904776) (@lem6904775 y)). Qed.
Lemma lem6904778 (y : int) (y' : int) : ((int_mul y y') = y') = ((int_mul y y') = y').
Proof. exact (eq_refl ((int_mul y y') = y')). Qed.
Lemma lem6904779 (y : int) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : int => @lem6904778 y y')). Qed.
Lemma lem6904780 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904781 (y : int) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6904780) (@lem6904779 y)). Qed.
Lemma lem6904782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6904783 (y : int) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6904782) (@lem6904781 y)). Qed.
Lemma lem6904784 (y : int) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6904783 y) (@lem6904777 y)). Qed.
Lemma lem6904785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6904786 (y : int) : (term59 y) = (term59 y).
Proof. exact (MK_COMB (@lem6904785) (@lem6904784 y)). Qed.
Lemma lem6904787 (y : int) : ((term40 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6904786 y) (@lem6904773 y)). Qed.
Lemma lem6904788 : term60 = term60.
Proof. exact (fun_ext (fun y : int => @lem6904787 y)). Qed.
Lemma lem6904789 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904790 : term61 = term61.
Proof. exact (MK_COMB (@lem6904789) (@lem6904788)). Qed.
Lemma lem6904791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904792 : term62 = term62.
Proof. exact (MK_COMB (@lem6904791) (@lem6904790)). Qed.
Lemma lem6904793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6904794 : term63 = term63.
Proof. exact (MK_COMB (@lem6904793) (@lem6904792)). Qed.
Lemma lem6904795 : term64 = term64.
Proof. exact (MK_COMB (@lem6904794) (@lem6904772)). Qed.
Lemma lem6904834 : term9 = term64.
Proof. exact (TRANS (@lem6904759) (@lem6904795)). Qed.
Lemma lem6904835 : term64 = term9.
Proof. exact (SYM (@lem6904834)). Qed.
Lemma lem6904836 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem6904837 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem6904838 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem6904840 (y : int) (y' : int) : ((int_mul y y') = y') = ((int_mul y y') = y').
Proof. exact (eq_refl ((int_mul y y') = y')). Qed.
Lemma lem6904841 (P : int -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6904842 (y : int) : (term72 y) = (term73 y).
Proof. exact (@lem6904841 (term19 y)). Qed.
Lemma lem6904843 (y : int) (y' : int) : (term21 y y') = ((int_mul y y') = y').
Proof. exact (eq_refl (term21 y y')). Qed.
Lemma lem6904844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904846 (y : int) (y' : int) : (term74 y y') = (term75 y y').
Proof. exact (MK_COMB (@lem6904844) (@lem6904843 y y')). Qed.
Lemma lem6904847 (y : int) : (term76 y) = (term77 y).
Proof. exact (fun_ext (fun y' : int => @lem6904846 y y')). Qed.
Lemma lem6904848 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6904849 (y : int) : (term73 y) = (term78 y).
Proof. exact (MK_COMB (@lem6904848) (@lem6904847 y)). Qed.
Lemma lem6904850 (y : int) : (term72 y) = (term78 y).
Proof. exact (TRANS (@lem6904842 y) (@lem6904849 y)). Qed.
Lemma lem6904851 (y : int) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : int => @lem6904840 y y')). Qed.
Lemma lem6904852 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904853 (y : int) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6904852) (@lem6904851 y)). Qed.
Lemma lem6904855 (y : int) (y' : int) : ((int_mul y' y) = y') = ((int_mul y' y) = y').
Proof. exact (eq_refl ((int_mul y' y) = y')). Qed.
Lemma lem6904856 (P : int -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6904857 (y : int) : (term79 y) = (term80 y).
Proof. exact (@lem6904856 (term20 y)). Qed.
Lemma lem6904858 (y : int) (y' : int) : (term24 y y') = ((int_mul y' y) = y').
Proof. exact (eq_refl (term24 y y')). Qed.
Lemma lem6904859 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904861 (y : int) (y' : int) : (term81 y y') = (term82 y y').
Proof. exact (MK_COMB (@lem6904859) (@lem6904858 y y')). Qed.
Lemma lem6904862 (y : int) : (term83 y) = (term84 y).
Proof. exact (fun_ext (fun y' : int => @lem6904861 y y')). Qed.
Lemma lem6904863 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6904864 (y : int) : (term80 y) = (term85 y).
Proof. exact (MK_COMB (@lem6904863) (@lem6904862 y)). Qed.
Lemma lem6904865 (y : int) : (term79 y) = (term85 y).
Proof. exact (TRANS (@lem6904857 y) (@lem6904864 y)). Qed.
Lemma lem6904866 (y : int) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : int => @lem6904855 y y')). Qed.
Lemma lem6904867 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6904868 (y : int) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6904867) (@lem6904866 y)). Qed.
Lemma lem6904869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6904870 (y : int) : (term86 y) = (term87 y).
Proof. exact (MK_COMB (@lem6904869) (@lem6904850 y)). Qed.
Lemma lem6904871 (y : int) : (term88 y) = (term89 y).
Proof. exact (MK_COMB (@lem6904870 y) (@lem6904865 y)). Qed.
Lemma lem6904872 (y : int) : (term90 y) = (term88 y).
Proof. exact (@lem17045 (term34 y) (term39 y)). Qed.
Lemma lem6904873 (y : int) : (term90 y) = (term89 y).
Proof. exact (TRANS (@lem6904872 y) (@lem6904871 y)). Qed.
Lemma lem6904874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6904875 (y : int) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6904874) (@lem6904853 y)). Qed.
Lemma lem6904876 (y : int) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6904875 y) (@lem6904868 y)). Qed.
Lemma lem6904877 (y : int) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem6904878 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6904879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6904880 (y : int) : (term92 y) = (term93 y).
Proof. exact (MK_COMB (@lem6904879) (@lem6904873 y)). Qed.
Lemma lem6904881 (y : int) : (term94 y) = (term95 y).
Proof. exact (MK_COMB (@lem6904880 y) (@lem6904878 y)). Qed.
Lemma lem6904882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6904883 (y : int) : (term96 y) = (term96 y).
Proof. exact (MK_COMB (@lem6904882) (@lem6904876 y)). Qed.
Lemma lem6904884 (y : int) : (term97 y) = (term97 y).
Proof. exact (MK_COMB (@lem6904883 y) (@lem6904877 y)). Qed.
Lemma lem6904885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6904886 (y : int) : (term98 y) = (term98 y).
Proof. exact (MK_COMB (@lem6904885) (@lem6904884 y)). Qed.
Lemma lem6904887 (y : int) : (term99 y) = (term100 y).
Proof. exact (MK_COMB (@lem6904886 y) (@lem6904881 y)). Qed.
Lemma lem6904888 (y : int) : (term101 y) = (term99 y).
Proof. exact (@lem17646 (term40 y) (y = term4)). Qed.
Lemma lem6904889 (y : int) : (term101 y) = (term100 y).
Proof. exact (TRANS (@lem6904888 y) (@lem6904887 y)). Qed.
Lemma lem6904890 (P : int -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6904891 : term62 = term102.
Proof. exact (@lem6904890 term60). Qed.
Lemma lem6904892 (y : int) : (term103 y) = ((term40 y) = (y = term4)).
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem6904893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6904894 (y : int) : (term104 y) = (term101 y).
Proof. exact (MK_COMB (@lem6904893) (@lem6904892 y)). Qed.
Lemma lem6904895 (y : int) : (term104 y) = (term100 y).
Proof. exact (TRANS (@lem6904894 y) (@lem6904889 y)). Qed.
Lemma lem6904896 : term105 = term106.
Proof. exact (fun_ext (fun y : int => @lem6904895 y)). Qed.
Lemma lem6904897 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6904898 : term102 = term107.
Proof. exact (MK_COMB (@lem6904897) (@lem6904896)). Qed.
Lemma lem6904899 : term62 = term107.
Proof. exact (TRANS (@lem6904891) (@lem6904898)). Qed.
Lemma lem6904901 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6904902 (P : int -> Prop) (Q : int -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem6904901 int P Q). Qed.
Lemma lem6904903 : term112 = term113.
Proof. exact (@lem6904902 term114 term115). Qed.
Lemma lem6904904 (y : int) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6904905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6904906 (y : int) : (term117 y) = (term98 y).
Proof. exact (MK_COMB (@lem6904905) (@lem6904904 y)). Qed.
Lemma lem6904907 (y : int) : (term118 y) = (term95 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem6904908 (y : int) : (term119 y) = (term100 y).
Proof. exact (MK_COMB (@lem6904906 y) (@lem6904907 y)). Qed.
Lemma lem6904909 : term120 = term106.
Proof. exact (fun_ext (fun y : int => @lem6904908 y)). Qed.
Lemma lem6904910 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6904911 : term112 = term107.
Proof. exact (MK_COMB (@lem6904910) (@lem6904909)). Qed.
Lemma lem6904912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6904913 : term121 = term122.
Proof. exact (MK_COMB (@lem6904912) (@lem6904911)). Qed.
Lemma lem6904914 (y : int) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6904915 : term123 = term114.
Proof. exact (fun_ext (fun y : int => @lem6904914 y)). Qed.
Lemma lem6904916 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6904917 : term124 = term125.
Proof. exact (MK_COMB (@lem6904916) (@lem6904915)). Qed.
Lemma lem6904918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6904919 : term126 = term127.
Proof. exact (MK_COMB (@lem6904918) (@lem6904917)). Qed.
Lemma lem6904920 (y : int) : (term118 y) = (term95 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem6904921 : term128 = term115.
Proof. exact (fun_ext (fun y : int => @lem6904920 y)). Qed.
Lemma lem6904922 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6904923 : term129 = term130.
Proof. exact (MK_COMB (@lem6904922) (@lem6904921)). Qed.
Lemma lem6904924 : term113 = term131.
Proof. exact (MK_COMB (@lem6904919) (@lem6904923)). Qed.
Lemma lem6904925 : (term112 = term113) = (term107 = term131).
Proof. exact (MK_COMB (@lem6904913) (@lem6904924)). Qed.
Lemma lem6904926 : term107 = term131.
Proof. exact (EQ_MP (@lem6904925) (@lem6904903)). Qed.
Lemma lem6905040 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6905041 (P : int -> Prop) (Q : int -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem6905040 int P Q). Qed.
Lemma lem6905042 (y : int) : (term132 y) = (term133 y).
Proof. exact (@lem6905041 (term77 y) (term84 y)). Qed.
Lemma lem6905043 (y : int) (y' : int) : (term134 y y') = (term75 y y').
Proof. exact (eq_refl (term134 y y')). Qed.
Lemma lem6905044 (y : int) : (term135 y) = (term77 y).
Proof. exact (fun_ext (fun y' : int => @lem6905043 y y')). Qed.
Lemma lem6905045 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905046 (y : int) : (term136 y) = (term78 y).
Proof. exact (MK_COMB (@lem6905045) (@lem6905044 y)). Qed.
Lemma lem6905047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6905048 (y : int) : (term137 y) = (term87 y).
Proof. exact (MK_COMB (@lem6905047) (@lem6905046 y)). Qed.
Lemma lem6905049 (y : int) (y' : int) : (term138 y y') = (term82 y y').
Proof. exact (eq_refl (term138 y y')). Qed.
Lemma lem6905050 (y : int) : (term139 y) = (term84 y).
Proof. exact (fun_ext (fun y' : int => @lem6905049 y y')). Qed.
Lemma lem6905051 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905052 (y : int) : (term140 y) = (term85 y).
Proof. exact (MK_COMB (@lem6905051) (@lem6905050 y)). Qed.
Lemma lem6905053 (y : int) : (term132 y) = (term89 y).
Proof. exact (MK_COMB (@lem6905048 y) (@lem6905052 y)). Qed.
Lemma lem6905054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905055 (y : int) : (term141 y) = (term142 y).
Proof. exact (MK_COMB (@lem6905054) (@lem6905053 y)). Qed.
Lemma lem6905056 (y : int) (y' : int) : (term134 y y') = (term75 y y').
Proof. exact (eq_refl (term134 y y')). Qed.
Lemma lem6905057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6905058 (y : int) (y' : int) : (term143 y y') = (term144 y y').
Proof. exact (MK_COMB (@lem6905057) (@lem6905056 y y')). Qed.
Lemma lem6905059 (y : int) (y' : int) : (term138 y y') = (term82 y y').
Proof. exact (eq_refl (term138 y y')). Qed.
Lemma lem6905060 (y : int) (y' : int) : (term145 y y') = (term146 y y').
Proof. exact (MK_COMB (@lem6905058 y y') (@lem6905059 y y')). Qed.
Lemma lem6905061 (y : int) : (term147 y) = (term148 y).
Proof. exact (fun_ext (fun y' : int => @lem6905060 y y')). Qed.
Lemma lem6905062 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905063 (y : int) : (term133 y) = (term149 y).
Proof. exact (MK_COMB (@lem6905062) (@lem6905061 y)). Qed.
Lemma lem6905064 (y : int) : ((term132 y) = (term133 y)) = ((term89 y) = (term149 y)).
Proof. exact (MK_COMB (@lem6905055 y) (@lem6905063 y)). Qed.
Lemma lem6905065 (y : int) : (term89 y) = (term149 y).
Proof. exact (EQ_MP (@lem6905064 y) (@lem6905042 y)). Qed.
Lemma lem6905066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6905067 (y : int) : (term93 y) = (term150 y).
Proof. exact (MK_COMB (@lem6905066) (@lem6905065 y)). Qed.
Lemma lem6905068 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6905069 (y : int) : (term95 y) = (term151 y).
Proof. exact (MK_COMB (@lem6905067 y) (@lem6905068 y)). Qed.
Lemma lem6905071 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6905072 (P : int -> Prop) (Q : Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem6905071 int P Q). Qed.
Lemma lem6905073 (y : int) : (term156 y) = (term157 y).
Proof. exact (@lem6905072 (term148 y) (y = term4)). Qed.
Lemma lem6905074 (y : int) (y' : int) : (term158 y y') = (term146 y y').
Proof. exact (eq_refl (term158 y y')). Qed.
Lemma lem6905075 (y : int) : (term159 y) = (term148 y).
Proof. exact (fun_ext (fun y' : int => @lem6905074 y y')). Qed.
Lemma lem6905076 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905077 (y : int) : (term160 y) = (term149 y).
Proof. exact (MK_COMB (@lem6905076) (@lem6905075 y)). Qed.
Lemma lem6905078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6905079 (y : int) : (term161 y) = (term150 y).
Proof. exact (MK_COMB (@lem6905078) (@lem6905077 y)). Qed.
Lemma lem6905080 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6905081 (y : int) : (term156 y) = (term151 y).
Proof. exact (MK_COMB (@lem6905079 y) (@lem6905080 y)). Qed.
Lemma lem6905082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905083 (y : int) : (term162 y) = (term163 y).
Proof. exact (MK_COMB (@lem6905082) (@lem6905081 y)). Qed.
Lemma lem6905084 (y : int) (y' : int) : (term158 y y') = (term146 y y').
Proof. exact (eq_refl (term158 y y')). Qed.
Lemma lem6905085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6905086 (y : int) (y' : int) : (term164 y y') = (term165 y y').
Proof. exact (MK_COMB (@lem6905085) (@lem6905084 y y')). Qed.
Lemma lem6905087 (y : int) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6905088 (y' : int) (y : int) : (term166 y' y) = (term167 y' y).
Proof. exact (MK_COMB (@lem6905086 y y') (@lem6905087 y)). Qed.
Lemma lem6905089 (y : int) : (term168 y) = (term169 y).
Proof. exact (fun_ext (fun y' : int => @lem6905088 y' y)). Qed.
Lemma lem6905090 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905091 (y : int) : (term157 y) = (term170 y).
Proof. exact (MK_COMB (@lem6905090) (@lem6905089 y)). Qed.
Lemma lem6905092 (y : int) : ((term156 y) = (term157 y)) = ((term151 y) = (term170 y)).
Proof. exact (MK_COMB (@lem6905083 y) (@lem6905091 y)). Qed.
Lemma lem6905093 (y : int) : (term151 y) = (term170 y).
Proof. exact (EQ_MP (@lem6905092 y) (@lem6905073 y)). Qed.
Lemma lem6905094 (y : int) : (term95 y) = (term170 y).
Proof. exact (TRANS (@lem6905069 y) (@lem6905093 y)). Qed.
Lemma lem6905095 : term115 = term171.
Proof. exact (fun_ext (fun y : int => @lem6905094 y)). Qed.
Lemma lem6905096 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905097 : term130 = term172.
Proof. exact (MK_COMB (@lem6905096) (@lem6905095)). Qed.
Lemma lem6905098 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem6905099 : term131 = term173.
Proof. exact (MK_COMB (@lem6905098) (@lem6905097)). Qed.
Lemma lem6905101 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6905102 (P : int -> Prop) (Q : int -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem6905101 int P Q). Qed.
Lemma lem6905103 : term174 = term175.
Proof. exact (@lem6905102 term114 term171). Qed.
Lemma lem6905104 (y : int) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6905105 : term123 = term114.
Proof. exact (fun_ext (fun y : int => @lem6905104 y)). Qed.
Lemma lem6905106 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905107 : term124 = term125.
Proof. exact (MK_COMB (@lem6905106) (@lem6905105)). Qed.
Lemma lem6905108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6905109 : term126 = term127.
Proof. exact (MK_COMB (@lem6905108) (@lem6905107)). Qed.
Lemma lem6905110 (y : int) : (term176 y) = (term170 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem6905111 : term177 = term171.
Proof. exact (fun_ext (fun y : int => @lem6905110 y)). Qed.
Lemma lem6905112 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905113 : term178 = term172.
Proof. exact (MK_COMB (@lem6905112) (@lem6905111)). Qed.
Lemma lem6905114 : term174 = term173.
Proof. exact (MK_COMB (@lem6905109) (@lem6905113)). Qed.
Lemma lem6905115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905116 : term179 = term180.
Proof. exact (MK_COMB (@lem6905115) (@lem6905114)). Qed.
Lemma lem6905117 (y : int) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6905118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6905119 (y : int) : (term117 y) = (term98 y).
Proof. exact (MK_COMB (@lem6905118) (@lem6905117 y)). Qed.
Lemma lem6905120 (y : int) : (term176 y) = (term170 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem6905121 (y : int) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem6905119 y) (@lem6905120 y)). Qed.
Lemma lem6905122 : term183 = term184.
Proof. exact (fun_ext (fun y : int => @lem6905121 y)). Qed.
Lemma lem6905123 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905124 : term175 = term185.
Proof. exact (MK_COMB (@lem6905123) (@lem6905122)). Qed.
Lemma lem6905125 : (term174 = term175) = (term173 = term185).
Proof. exact (MK_COMB (@lem6905116) (@lem6905124)). Qed.
Lemma lem6905126 : term173 = term185.
Proof. exact (EQ_MP (@lem6905125) (@lem6905103)). Qed.
Lemma lem6905128 {A : Type'} (P : Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6905129 (P : Prop) (Q : int -> Prop) : (term188 P Q) = (term189 P Q).
Proof. exact (@lem6905128 int P Q). Qed.
Lemma lem6905130 (y : int) : (term190 y) = (term191 y).
Proof. exact (@lem6905129 (term97 y) (term169 y)). Qed.
Lemma lem6905131 (y' : int) (y : int) : (term192 y y') = (term167 y' y).
Proof. exact (eq_refl (term192 y y')). Qed.
Lemma lem6905132 (y : int) : (term193 y) = (term169 y).
Proof. exact (fun_ext (fun y' : int => @lem6905131 y' y)). Qed.
Lemma lem6905133 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905134 (y : int) : (term194 y) = (term170 y).
Proof. exact (MK_COMB (@lem6905133) (@lem6905132 y)). Qed.
Lemma lem6905135 (y : int) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem6905136 (y : int) : (term190 y) = (term182 y).
Proof. exact (MK_COMB (@lem6905135 y) (@lem6905134 y)). Qed.
Lemma lem6905137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905138 (y : int) : (term195 y) = (term196 y).
Proof. exact (MK_COMB (@lem6905137) (@lem6905136 y)). Qed.
Lemma lem6905139 (y' : int) (y : int) : (term192 y y') = (term167 y' y).
Proof. exact (eq_refl (term192 y y')). Qed.
Lemma lem6905140 (y : int) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem6905141 (y' : int) (y : int) : (term197 y y') = (term198 y' y).
Proof. exact (MK_COMB (@lem6905140 y) (@lem6905139 y' y)). Qed.
Lemma lem6905142 (y : int) : (term199 y) = (term200 y).
Proof. exact (fun_ext (fun y' : int => @lem6905141 y' y)). Qed.
Lemma lem6905143 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905144 (y : int) : (term191 y) = (term201 y).
Proof. exact (MK_COMB (@lem6905143) (@lem6905142 y)). Qed.
Lemma lem6905145 (y : int) : ((term190 y) = (term191 y)) = ((term182 y) = (term201 y)).
Proof. exact (MK_COMB (@lem6905138 y) (@lem6905144 y)). Qed.
Lemma lem6905146 (y : int) : (term182 y) = (term201 y).
Proof. exact (EQ_MP (@lem6905145 y) (@lem6905130 y)). Qed.
Lemma lem6905147 : term184 = term202.
Proof. exact (fun_ext (fun y : int => @lem6905146 y)). Qed.
Lemma lem6905148 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6905149 : term185 = term203.
Proof. exact (MK_COMB (@lem6905148) (@lem6905147)). Qed.
Lemma lem6905150 : term173 = term203.
Proof. exact (TRANS (@lem6905126) (@lem6905149)). Qed.
Lemma lem6905151 : term131 = term203.
Proof. exact (TRANS (@lem6905099) (@lem6905150)). Qed.
Lemma lem6905152 : term107 = term203.
Proof. exact (TRANS (@lem6904926) (@lem6905151)). Qed.
Lemma lem6905153 : term62 = term203.
Proof. exact (TRANS (@lem6904899) (@lem6905152)). Qed.
Lemma lem6905154 (h1 : term62) : term203.
Proof. exact (EQ_MP (@lem6905153) (@lem6904836 h1)). Qed.
Lemma lem6905155 (x : int) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6905156 : term68 = term68.
Proof. exact (fun_ext (fun x : int => @lem6905155 x)). Qed.
Lemma lem6905157 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905166 : term69 = term69.
Proof. exact (MK_COMB (@lem6905157) (@lem6905156)). Qed.
Lemma lem6905167 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem6905166) (@lem6904837 h1)). Qed.
Lemma lem6905168 (x : int) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6905169 : term66 = term66.
Proof. exact (fun_ext (fun x : int => @lem6905168 x)). Qed.
Lemma lem6905170 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905179 : term54 = term54.
Proof. exact (MK_COMB (@lem6905170) (@lem6905169)). Qed.
Lemma lem6905180 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6905179) (@lem6904838 h1)). Qed.
Lemma lem6905181 (y : int) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem6905182 (y' : int) (y : int) (h1 : term198 y' y) : term198 y' y.
Proof. exact (h1). Qed.
Lemma lem6905197 (x : int) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6905198 : term68 = term68.
Proof. exact (fun_ext (fun x : int => @lem6905197 x)). Qed.
Lemma lem6905199 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905200 : term69 = term69.
Proof. exact (MK_COMB (@lem6905199) (@lem6905198)). Qed.
Lemma lem6905201 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem6905200) (@lem6905167 h1)). Qed.
Lemma lem6905216 (x : int) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6905217 : term66 = term66.
Proof. exact (fun_ext (fun x : int => @lem6905216 x)). Qed.
Lemma lem6905218 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905219 : term54 = term54.
Proof. exact (MK_COMB (@lem6905218) (@lem6905217)). Qed.
Lemma lem6905220 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6905219) (@lem6905180 h1)). Qed.
Lemma lem6905259 (y' : int) (y : int) : (term167 y' y) = (term167 y' y).
Proof. exact (eq_refl (term167 y' y)). Qed.
Lemma lem6905272 (y : int) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem6905281 (y : int) (y' : int) : ((int_mul y' y) = y') = ((int_mul y' y) = y').
Proof. exact (eq_refl ((int_mul y' y) = y')). Qed.
Lemma lem6905282 (y : int) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : int => @lem6905281 y y')). Qed.
Lemma lem6905283 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905284 (y : int) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6905283) (@lem6905282 y)). Qed.
Lemma lem6905293 (y : int) (y' : int) : ((int_mul y y') = y') = ((int_mul y y') = y').
Proof. exact (eq_refl ((int_mul y y') = y')). Qed.
Lemma lem6905294 (y : int) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : int => @lem6905293 y y')). Qed.
Lemma lem6905295 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905296 (y : int) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6905295) (@lem6905294 y)). Qed.
Lemma lem6905297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6905298 (y : int) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6905297) (@lem6905296 y)). Qed.
Lemma lem6905299 (y : int) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6905298 y) (@lem6905284 y)). Qed.
Lemma lem6905300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6905301 (y : int) : (term96 y) = (term96 y).
Proof. exact (MK_COMB (@lem6905300) (@lem6905299 y)). Qed.
Lemma lem6905302 (y : int) : (term97 y) = (term97 y).
Proof. exact (MK_COMB (@lem6905301 y) (@lem6905272 y)). Qed.
Lemma lem6905303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6905304 (y : int) : (term98 y) = (term98 y).
Proof. exact (MK_COMB (@lem6905303) (@lem6905302 y)). Qed.
Lemma lem6905305 (y' : int) (y : int) : (term198 y' y) = (term198 y' y).
Proof. exact (MK_COMB (@lem6905304 y) (@lem6905259 y' y)). Qed.
Lemma lem6905306 (y' : int) (y : int) (h1 : term198 y' y) : term198 y' y.
Proof. exact (EQ_MP (@lem6905305 y' y) (@lem6905182 y' y h1)). Qed.
Lemma lem6905307 (y : int) (h1 : term97 y) : term97 y.
Proof. exact (h1). Qed.
Lemma lem6905308 (y' : int) (y : int) (h1 : term167 y' y) : term167 y' y.
Proof. exact (h1). Qed.
Lemma lem6905310 (y : int) (h1 : term97 y) : term40 y.
Proof. exact (proj1 (@lem6905307 y h1)). Qed.
Lemma lem6905311 (y : int) (h1 : term97 y) : term39 y.
Proof. exact (proj2 (@lem6905310 y h1)). Qed.
Lemma lem6905314 (y' : int) (y : int) (h1 : term167 y' y) : term146 y y'.
Proof. exact (proj1 (@lem6905308 y' y h1)). Qed.
Lemma lem6905325 (x : int) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6905326 : term66 = term66.
Proof. exact (fun_ext (fun x : int => @lem6905325 x)). Qed.
Lemma lem6905327 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905329 : term54 = term54.
Proof. exact (MK_COMB (@lem6905327) (@lem6905326)). Qed.
Lemma lem6905330 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6905329) (@lem6905220 h1)). Qed.
Lemma lem6905343 (y : int) (y' : int) : ((int_mul y' y) = y') = ((int_mul y' y) = y').
Proof. exact (eq_refl ((int_mul y' y) = y')). Qed.
Lemma lem6905344 (y : int) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : int => @lem6905343 y y')). Qed.
Lemma lem6905345 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905347 (y : int) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6905345) (@lem6905344 y)). Qed.
Lemma lem6905348 (y : int) (h1 : term97 y) : term39 y.
Proof. exact (EQ_MP (@lem6905347 y) (@lem6905311 y h1)). Qed.
Lemma lem6905357 (x : int) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6905358 : term66 = term66.
Proof. exact (fun_ext (fun x : int => @lem6905357 x)). Qed.
Lemma lem6905359 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905361 : term54 = term54.
Proof. exact (MK_COMB (@lem6905359) (@lem6905358)). Qed.
Lemma lem6905362 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6905361) (@lem6905220 h1)). Qed.
Lemma lem6905370 (y : int) (y' : int) (h1 : term75 y y') : term75 y y'.
Proof. exact (h1). Qed.
Lemma lem6905372 (x : int) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6905373 : term68 = term68.
Proof. exact (fun_ext (fun x : int => @lem6905372 x)). Qed.
Lemma lem6905374 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905376 : term69 = term69.
Proof. exact (MK_COMB (@lem6905374) (@lem6905373)). Qed.
Lemma lem6905377 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem6905376) (@lem6905201 h1)). Qed.
Lemma lem6905392 (y : int) (y' : int) (h1 : term82 y y') : term82 y y'.
Proof. exact (h1). Qed.
Lemma lem6905396 (_92169 : int) (h1 : term54) : term204 _92169.
Proof. exact (@lem6905330 h1 _92169). Qed.
Lemma lem6905397 (_92169 : int) : (term204 _92169) = ((term65 _92169) = _92169).
Proof. exact (eq_refl (term204 _92169)). Qed.
Lemma lem6905402 (_92171 : int) (y : int) (h1 : term97 y) : term24 y _92171.
Proof. exact (@lem6905348 y h1 _92171). Qed.
Lemma lem6905403 (y : int) (_92171 : int) : (term24 y _92171) = ((int_mul _92171 y) = _92171).
Proof. exact (eq_refl (term24 y _92171)). Qed.
Lemma lem6905408 (_92173 : int) (h1 : term54) : term204 _92173.
Proof. exact (@lem6905362 h1 _92173). Qed.
Lemma lem6905409 (_92173 : int) : (term204 _92173) = ((term65 _92173) = _92173).
Proof. exact (eq_refl (term204 _92173)). Qed.
Lemma lem6905411 (_92174 : int) (h1 : term69) : term205 _92174.
Proof. exact (@lem6905377 h1 _92174). Qed.
Lemma lem6905412 (_92174 : int) : (term205 _92174) = ((term67 _92174) = _92174).
Proof. exact (eq_refl (term205 _92174)). Qed.
Lemma lem6905422 (y : int) (h1 : term97 y) : term91 y.
Proof. exact (proj2 (@lem6905307 y h1)). Qed.
Lemma lem6905432 (y' : int) (y : int) (h1 : term167 y' y) : y = term4.
Proof. exact (proj2 (@lem6905308 y' y h1)). Qed.
Lemma lem6905434 (y : int) (y' : int) (h1 : term75 y y') : term75 y y'.
Proof. exact (h1). Qed.
Lemma lem6905440 (y' : int) (y : int) (h1 : term167 y' y) : y = term4.
Proof. exact (proj2 (@lem6905308 y' y h1)). Qed.
Lemma lem6905442 (y : int) (y' : int) (h1 : term82 y y') : term82 y y'.
Proof. exact (h1). Qed.
Lemma lem6905485 (y' : int) : (term206 y') = (term206 y').
Proof. exact (eq_refl (term206 y')). Qed.
Lemma lem6905486 (y' : int) (y : int) (h1 : term167 y' y) : (term207 y' y) = (term208 y').
Proof. exact (MK_COMB (@lem6905485 y') (@lem6905432 y' y h1)). Qed.
Lemma lem6905487 (y' : int) : (term208 y') = (term209 y').
Proof. exact (eq_refl (term208 y')). Qed.
Lemma lem6905488 (y' : int) (y : int) : (term210 y' y) = (term210 y' y).
Proof. exact (eq_refl (term210 y' y)). Qed.
Lemma lem6905489 (y : int) (y' : int) : ((term207 y' y) = (term208 y')) = ((term207 y' y) = (term209 y')).
Proof. exact (MK_COMB (@lem6905488 y' y) (@lem6905487 y')). Qed.
Lemma lem6905490 (y : int) (y' : int) : (term207 y' y) = (term75 y y').
Proof. exact (eq_refl (term207 y' y)). Qed.
Lemma lem6905491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905492 (y : int) (y' : int) : (term210 y' y) = (term211 y y').
Proof. exact (MK_COMB (@lem6905491) (@lem6905490 y y')). Qed.
Lemma lem6905493 (y' : int) : (term209 y') = (term209 y').
Proof. exact (eq_refl (term209 y')). Qed.
Lemma lem6905494 (y : int) (y' : int) : ((term207 y' y) = (term209 y')) = ((term75 y y') = (term209 y')).
Proof. exact (MK_COMB (@lem6905492 y y') (@lem6905493 y')). Qed.
Lemma lem6905495 (y : int) (y' : int) : ((term207 y' y) = (term208 y')) = ((term75 y y') = (term209 y')).
Proof. exact (TRANS (@lem6905489 y y') (@lem6905494 y y')). Qed.
Lemma lem6905496 (y' : int) (y : int) (h1 : term167 y' y) : (term75 y y') = (term209 y').
Proof. exact (EQ_MP (@lem6905495 y y') (@lem6905486 y' y h1)). Qed.
Lemma lem6905497 (y' : int) (y : int) (h1 : term75 y y') (h2 : term167 y' y) : term209 y'.
Proof. exact (EQ_MP (@lem6905496 y' y h2) (@lem6905434 y y' h1)). Qed.
Lemma lem6905540 (y' : int) : (term212 y') = (term212 y').
Proof. exact (eq_refl (term212 y')). Qed.
Lemma lem6905541 (y' : int) (y : int) (h1 : term167 y' y) : (term213 y' y) = (term214 y').
Proof. exact (MK_COMB (@lem6905540 y') (@lem6905440 y' y h1)). Qed.
Lemma lem6905542 (y' : int) : (term214 y') = (term215 y').
Proof. exact (eq_refl (term214 y')). Qed.
Lemma lem6905543 (y' : int) (y : int) : (term216 y' y) = (term216 y' y).
Proof. exact (eq_refl (term216 y' y)). Qed.
Lemma lem6905544 (y : int) (y' : int) : ((term213 y' y) = (term214 y')) = ((term213 y' y) = (term215 y')).
Proof. exact (MK_COMB (@lem6905543 y' y) (@lem6905542 y')). Qed.
Lemma lem6905545 (y : int) (y' : int) : (term213 y' y) = (term82 y y').
Proof. exact (eq_refl (term213 y' y)). Qed.
Lemma lem6905546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905547 (y : int) (y' : int) : (term216 y' y) = (term217 y y').
Proof. exact (MK_COMB (@lem6905546) (@lem6905545 y y')). Qed.
Lemma lem6905548 (y' : int) : (term215 y') = (term215 y').
Proof. exact (eq_refl (term215 y')). Qed.
Lemma lem6905549 (y : int) (y' : int) : ((term213 y' y) = (term215 y')) = ((term82 y y') = (term215 y')).
Proof. exact (MK_COMB (@lem6905547 y y') (@lem6905548 y')). Qed.
Lemma lem6905550 (y : int) (y' : int) : ((term213 y' y) = (term214 y')) = ((term82 y y') = (term215 y')).
Proof. exact (TRANS (@lem6905544 y y') (@lem6905549 y y')). Qed.
Lemma lem6905551 (y' : int) (y : int) (h1 : term167 y' y) : (term82 y y') = (term215 y').
Proof. exact (EQ_MP (@lem6905550 y y') (@lem6905541 y' y h1)). Qed.
Lemma lem6905552 (y' : int) (y : int) (h1 : term82 y y') (h2 : term167 y' y) : term215 y'.
Proof. exact (EQ_MP (@lem6905551 y' y h2) (@lem6905442 y y' h1)). Qed.
Lemma lem6905593 (x : int) (y : int) (z : int) : term218 x y z.
Proof. exact (@lem21385 int x y z). Qed.
Lemma lem6905597 (_92169 : int) (h1 : term54) : (term65 _92169) = _92169.
Proof. exact (EQ_MP (@lem6905397 _92169) (@lem6905396 _92169 h1)). Qed.
Lemma lem6905598 (y : int) (h1 : term54) : (term65 y) = y.
Proof. exact (@lem6905597 y h1). Qed.
Lemma lem6905599 (y : int) (h1 : term54) : term219 y.
Proof. exact (fun h0 : term209 y => @lem6905598 y h1). Qed.
Lemma lem6905601 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905602 (y : int) : (term219 y) = ((term65 y) = y).
Proof. exact (@lem6905601 ((term65 y) = y)). Qed.
Lemma lem6905603 (y : int) (h1 : term54) : (term65 y) = y.
Proof. exact (EQ_MP (@lem6905602 y) (@lem6905599 y h1)). Qed.
Lemma lem6905605 (_92171 : int) (y : int) (h1 : term97 y) : (int_mul _92171 y) = _92171.
Proof. exact (EQ_MP (@lem6905403 y _92171) (@lem6905402 _92171 y h1)). Qed.
Lemma lem6905606 (y : int) (h1 : term97 y) : (term65 y) = term4.
Proof. exact (@lem6905605 term4 y h1). Qed.
Lemma lem6905607 (y : int) (h1 : term97 y) : term221 y.
Proof. exact (fun h0 : term222 y => @lem6905606 y h1). Qed.
Lemma lem6905609 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905610 (y : int) : (term221 y) = ((term65 y) = term4).
Proof. exact (@lem6905609 ((term65 y) = term4)). Qed.
Lemma lem6905611 (y : int) (h1 : term97 y) : (term65 y) = term4.
Proof. exact (EQ_MP (@lem6905610 y) (@lem6905607 y h1)). Qed.
Lemma lem6905629 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6905630 (y : int) (x : int) (z : int) : (term223 x y z) = (term224 y x z).
Proof. exact (@lem6905629 (y = z) (term225 x z)). Qed.
Lemma lem6905640 (x : int) (y : int) : (term226 x y) = (term226 x y).
Proof. exact (eq_refl (term226 x y)). Qed.
Lemma lem6905641 (y : int) (x : int) (z : int) : (term218 x y z) = (term227 y x z).
Proof. exact (MK_COMB (@lem6905640 x y) (@lem6905630 y x z)). Qed.
Lemma lem6905645 (q : Prop) (p : Prop) (r : Prop) : (term228 p q r) = (term228 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6905646 (y : int) (x : int) (z : int) : (term227 y x z) = (term229 y x z).
Proof. exact (@lem6905645 (y = z) (term225 x y) (term225 x z)). Qed.
Lemma lem6905668 (y : int) (x : int) (z : int) : (term218 x y z) = (term229 y x z).
Proof. exact (TRANS (@lem6905641 y x z) (@lem6905646 y x z)). Qed.
Lemma lem6905669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6905670 (y : int) (x : int) (z : int) : (term230 x y z) = (term231 y x z).
Proof. exact (MK_COMB (@lem6905669) (@lem6905668 y x z)). Qed.
Lemma lem6905692 (y : int) (x : int) (z : int) : (term229 y x z) = (term229 y x z).
Proof. exact (eq_refl (term229 y x z)). Qed.
Lemma lem6905693 (y : int) (x : int) (z : int) : ((term218 x y z) = (term229 y x z)) = ((term229 y x z) = (term229 y x z)).
Proof. exact (MK_COMB (@lem6905670 y x z) (@lem6905692 y x z)). Qed.
Lemma lem6905695 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6905696 (x : Prop) : (x = x) = True.
Proof. exact (@lem6905695 Prop x). Qed.
Lemma lem6905697 (y : int) (x : int) (z : int) : ((term229 y x z) = (term229 y x z)) = True.
Proof. exact (@lem6905696 (term229 y x z)). Qed.
Lemma lem6905698 (y : int) (x : int) (z : int) : ((term218 x y z) = (term229 y x z)) = True.
Proof. exact (TRANS (@lem6905693 y x z) (@lem6905697 y x z)). Qed.
Lemma lem6905699 (y : int) (x : int) (z : int) : True = ((term218 x y z) = (term229 y x z)).
Proof. exact (SYM (@lem6905698 y x z)). Qed.
Lemma lem6905700 (y : int) (x : int) (z : int) : (term218 x y z) = (term229 y x z).
Proof. exact (EQ_MP (@lem6905699 y x z) (@lem0)). Qed.
Lemma lem6905701 (y : int) (x : int) (z : int) : term229 y x z.
Proof. exact (EQ_MP (@lem6905700 y x z) (@lem6905593 x y z)). Qed.
Lemma lem6905703 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6905704 (x : int) (y : int) (z : int) : (term229 y x z) = (term233 x y z).
Proof. exact (@lem6905703 (term234 y x z) (y = z)). Qed.
Lemma lem6905706 (a : Prop) (b : Prop) : (term235 a b) = (term236 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6905707 (y : int) (x : int) (z : int) : (term237 y x z) = (term238 y x z).
Proof. exact (@lem6905706 (term225 x y) (term225 x z)). Qed.
Lemma lem6905709 (a : Prop) : (term239 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6905710 (x : int) (y : int) : (term240 x y) = (x = y).
Proof. exact (@lem6905709 (x = y)). Qed.
Lemma lem6905711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6905712 (x : int) (y : int) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem6905711) (@lem6905710 x y)). Qed.
Lemma lem6905714 (a : Prop) : (term239 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6905715 (x : int) (z : int) : (term240 x z) = (x = z).
Proof. exact (@lem6905714 (x = z)). Qed.
Lemma lem6905716 (y : int) (x : int) (z : int) : (term238 y x z) = (term243 y x z).
Proof. exact (MK_COMB (@lem6905712 x y) (@lem6905715 x z)). Qed.
Lemma lem6905717 (y : int) (x : int) (z : int) : (term237 y x z) = (term243 y x z).
Proof. exact (TRANS (@lem6905707 y x z) (@lem6905716 y x z)). Qed.
Lemma lem6905718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6905719 (y : int) (x : int) (z : int) : (term244 y x z) = (term245 y x z).
Proof. exact (MK_COMB (@lem6905718) (@lem6905717 y x z)). Qed.
Lemma lem6905720 (y : int) (z : int) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6905721 (x : int) (y : int) (z : int) : (term233 x y z) = (term246 x y z).
Proof. exact (MK_COMB (@lem6905719 y x z) (@lem6905720 y z)). Qed.
Lemma lem6905722 (x : int) (y : int) (z : int) : (term229 y x z) = (term246 x y z).
Proof. exact (TRANS (@lem6905704 x y z) (@lem6905721 x y z)). Qed.
Lemma lem6905724 (y : int) (h1 : term54) (h2 : term97 y) : term247 y.
Proof. exact (conj (@lem6905603 y h1) (@lem6905611 y h2)). Qed.
Lemma lem6905726 (x : int) (y : int) (z : int) : term246 x y z.
Proof. exact (EQ_MP (@lem6905722 x y z) (@lem6905701 y x z)). Qed.
Lemma lem6905727 (y : int) : term248 y.
Proof. exact (@lem6905726 (term65 y) y term4). Qed.
Lemma lem6905730 (y : int) (h1 : term54) (h2 : term97 y) : y = term4.
Proof. exact (@lem6905727 y (@lem6905724 y h1 h2)). Qed.
Lemma lem6905731 (y : int) (h1 : term54) (h2 : term97 y) : term249 y.
Proof. exact (fun h0 : term91 y => @lem6905730 y h1 h2). Qed.
Lemma lem6905733 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905734 (y : int) : (term249 y) = (y = term4).
Proof. exact (@lem6905733 (y = term4)). Qed.
Lemma lem6905735 (y : int) (h1 : term54) (h2 : term97 y) : y = term4.
Proof. exact (EQ_MP (@lem6905734 y) (@lem6905731 y h1 h2)). Qed.
Lemma lem6905738 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6905740 (y : int) : (term91 y) = (term250 y).
Proof. exact (@lem6905738 (y = term4)). Qed.
Lemma lem6905743 (y : int) (h1 : term97 y) : term250 y.
Proof. exact (EQ_MP (@lem6905740 y) (@lem6905422 y h1)). Qed.
Lemma lem6905746 (y : int) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (@lem6905743 y h2 (@lem6905735 y h1 h2)). Qed.
Lemma lem6905747 (y : int) (h1 : term54) (h2 : term97 y) : term251.
Proof. exact (fun h0 : ~ False => @lem6905746 y h1 h2). Qed.
Lemma lem6905749 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905750 : term251 = False.
Proof. exact (@lem6905749 False). Qed.
Lemma lem6905751 (y : int) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (EQ_MP (@lem6905750) (@lem6905747 y h1 h2)). Qed.
Lemma lem6905796 (_92173 : int) (h1 : term54) : (term65 _92173) = _92173.
Proof. exact (EQ_MP (@lem6905409 _92173) (@lem6905408 _92173 h1)). Qed.
Lemma lem6905797 (y' : int) (h1 : term54) : (term65 y') = y'.
Proof. exact (@lem6905796 y' h1). Qed.
Lemma lem6905798 (y' : int) (h1 : term54) : term219 y'.
Proof. exact (fun h0 : term209 y' => @lem6905797 y' h1). Qed.
Lemma lem6905800 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905801 (y' : int) : (term219 y') = ((term65 y') = y').
Proof. exact (@lem6905800 ((term65 y') = y')). Qed.
Lemma lem6905802 (y' : int) (h1 : term54) : (term65 y') = y'.
Proof. exact (EQ_MP (@lem6905801 y') (@lem6905798 y' h1)). Qed.
Lemma lem6905805 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6905807 (y' : int) : (term209 y') = (term252 y').
Proof. exact (@lem6905805 ((term65 y') = y')). Qed.
Lemma lem6905810 (y' : int) (y : int) (h1 : term75 y y') (h2 : term167 y' y) : term252 y'.
Proof. exact (EQ_MP (@lem6905807 y') (@lem6905497 y' y h1 h2)). Qed.
Lemma lem6905813 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (@lem6905810 y' y h2 h3 (@lem6905802 y' h1)). Qed.
Lemma lem6905814 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : term251.
Proof. exact (fun h0 : ~ False => @lem6905813 y' y h1 h2 h3). Qed.
Lemma lem6905816 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905817 : term251 = False.
Proof. exact (@lem6905816 False). Qed.
Lemma lem6905863 (_92174 : int) (h1 : term69) : (term67 _92174) = _92174.
Proof. exact (EQ_MP (@lem6905412 _92174) (@lem6905411 _92174 h1)). Qed.
Lemma lem6905864 (y' : int) (h1 : term69) : (term67 y') = y'.
Proof. exact (@lem6905863 y' h1). Qed.
Lemma lem6905865 (y' : int) (h1 : term69) : term253 y'.
Proof. exact (fun h0 : term215 y' => @lem6905864 y' h1). Qed.
Lemma lem6905867 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905868 (y' : int) : (term253 y') = ((term67 y') = y').
Proof. exact (@lem6905867 ((term67 y') = y')). Qed.
Lemma lem6905869 (y' : int) (h1 : term69) : (term67 y') = y'.
Proof. exact (EQ_MP (@lem6905868 y') (@lem6905865 y' h1)). Qed.
Lemma lem6905872 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6905874 (y' : int) : (term215 y') = (term254 y').
Proof. exact (@lem6905872 ((term67 y') = y')). Qed.
Lemma lem6905877 (y' : int) (y : int) (h1 : term82 y y') (h2 : term167 y' y) : term254 y'.
Proof. exact (EQ_MP (@lem6905874 y') (@lem6905552 y' y h1 h2)). Qed.
Lemma lem6905880 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (@lem6905877 y' y h2 h3 (@lem6905869 y' h1)). Qed.
Lemma lem6905881 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : term251.
Proof. exact (fun h0 : ~ False => @lem6905880 y' y h1 h2 h3). Qed.
Lemma lem6905883 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6905884 : term251 = False.
Proof. exact (@lem6905883 False). Qed.
Lemma lem6905886 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905884) (@lem6905881 y' y h1 h2 h3)). Qed.
Lemma lem6905887 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905817) (@lem6905814 y' y h1 h2 h3)). Qed.
Lemma lem6905888 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem6905886 y' y h1 h2 h3) (fun h4 : False => @lem6905442 y y' h2)). Qed.
Lemma lem6905889 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905888 y' y h1 h2 h3) (@lem6905442 y y' h2)). Qed.
Lemma lem6905890 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem6905887 y' y h1 h2 h3) (fun h4 : False => @lem6905434 y y' h2)). Qed.
Lemma lem6905891 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905890 y' y h1 h2 h3) (@lem6905434 y y' h2)). Qed.
Lemma lem6905892 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem6905889 y' y h1 h2 h3) (fun h4 : False => @lem6905392 y y' h2)). Qed.
Lemma lem6905893 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905892 y' y h1 h2 h3) (@lem6905392 y y' h2)). Qed.
Lemma lem6905894 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem6905891 y' y h1 h2 h3) (fun h4 : False => @lem6905370 y y' h2)). Qed.
Lemma lem6905895 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905894 y' y h1 h2 h3) (@lem6905370 y y' h2)). Qed.
Lemma lem6905896 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem6905893 y' y h1 h2 h3) (fun h4 : False => @lem6905392 y y' h2)). Qed.
Lemma lem6905897 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905896 y' y h1 h2 h3) (@lem6905392 y y' h2)). Qed.
Lemma lem6905898 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem6905897 y' y h1 h2 h3) (fun h4 : False => @lem6905377 h1)). Qed.
Lemma lem6905899 (y' : int) (y : int) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905898 y' y h1 h2 h3) (@lem6905377 h1)). Qed.
Lemma lem6905900 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem6905895 y' y h1 h2 h3) (fun h4 : False => @lem6905370 y y' h2)). Qed.
Lemma lem6905901 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905900 y' y h1 h2 h3) (@lem6905370 y y' h2)). Qed.
Lemma lem6905902 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6905901 y' y h1 h2 h3) (fun h4 : False => @lem6905362 h1)). Qed.
Lemma lem6905903 (y' : int) (y : int) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6905902 y' y h1 h2 h3) (@lem6905362 h1)). Qed.
Lemma lem6905904 (y : int) (h1 : term54) (h2 : term97 y) : term54 = False.
Proof. exact (prop_ext (fun h3 : term54 => @lem6905751 y h1 h2) (fun h3 : False => @lem6905330 h1)). Qed.
Lemma lem6905905 (y : int) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (EQ_MP (@lem6905904 y h1 h2) (@lem6905330 h1)). Qed.
Lemma lem6905906 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term167 y' y) : False.
Proof. exact (or_elim (@lem6905314 y' y h3) (fun h0 : term75 y y' => @lem6905903 y' y h2 h0 h3) (fun h0 : term82 y y' => @lem6905899 y' y h1 h0 h3)). Qed.
Lemma lem6905907 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (or_elim (@lem6905306 y' y h3) (fun h0 : term97 y => @lem6905905 y h2 h0) (fun h0 : term167 y' y => @lem6905906 y' y h1 h2 h0)). Qed.
Lemma lem6905908 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : (term198 y' y) = False.
Proof. exact (prop_ext (fun h4 : term198 y' y => @lem6905907 y' y h1 h2 h3) (fun h4 : False => @lem6905306 y' y h3)). Qed.
Lemma lem6905909 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem6905908 y' y h1 h2 h3) (@lem6905306 y' y h3)). Qed.
Lemma lem6905910 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6905909 y' y h1 h2 h3) (fun h4 : False => @lem6905220 h2)). Qed.
Lemma lem6905911 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem6905910 y' y h1 h2 h3) (@lem6905220 h2)). Qed.
Lemma lem6905912 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem6905911 y' y h1 h2 h3) (fun h4 : False => @lem6905201 h1)). Qed.
Lemma lem6905913 (y' : int) (y : int) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem6905912 y' y h1 h2 h3) (@lem6905201 h1)). Qed.
Lemma lem6905914 (y : int) (h1 : term69) (h2 : term54) (h3 : term201 y) : False.
Proof. exact (ex_elim (@lem6905181 y h3) (fun y' : int => fun h0 : term200 y y' => @lem6905913 y' y h1 h2 h0)). Qed.
Lemma lem6905915 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (ex_elim (@lem6905154 h3) (fun y : int => fun h0 : term202 y => @lem6905914 y h1 h2 h0)). Qed.
Lemma lem6905916 (h1 : term69) (h2 : term54) (h3 : term62) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6905915 h1 h2 h3) (fun h4 : False => @lem6905180 h2)). Qed.
Lemma lem6905917 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (EQ_MP (@lem6905916 h1 h2 h3) (@lem6905180 h2)). Qed.
Lemma lem6905918 (h1 : term69) (h2 : term54) (h3 : term62) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem6905917 h1 h2 h3) (fun h4 : False => @lem6905167 h1)). Qed.
Lemma lem6905919 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (EQ_MP (@lem6905918 h1 h2 h3) (@lem6905167 h1)). Qed.
Lemma lem6905920 (h1 : term69) (h2 : term62) : term52.
Proof. exact (fun h0 : term54 => @lem6905919 h1 h0 h2). Qed.
Lemma lem6905921 : term52 = term53.
Proof. exact (@lem69 term54). Qed.
Lemma lem6905922 (h1 : term69) (h2 : term62) : term53.
Proof. exact (EQ_MP (@lem6905921) (@lem6905920 h1 h2)). Qed.
Lemma lem6905923 (h1 : term62) : term57.
Proof. exact (fun h0 : term69 => @lem6905922 h0 h1). Qed.
Lemma lem6905924 : term64.
Proof. exact (fun h0 : term62 => @lem6905923 h0). Qed.
Lemma lem6905925 : term9.
Proof. exact (EQ_MP (@lem6904835) (@lem6905924)). Qed.
Lemma lem6905927 : term9.
Proof. exact (@lem6904661 (@lem6905925)). Qed.
Lemma lem6905928 (h1 : term8) : term56.
Proof. exact (@lem6905927 (@lem6904646 h1)). Qed.
Lemma lem6905929 (h1 : term8) : term52.
Proof. exact (@lem6905928 h1 (@lem2306233)). Qed.
Lemma lem6905930 (h1 : term8) : False.
Proof. exact (@lem6905929 h1 (@lem2305981)). Qed.
Lemma lem6905931 (h1 : term8) : term8 = False.
Proof. exact (prop_ext (fun h2 : term8 => @lem6905930 h1) (fun h2 : False => @lem6904646 h1)). Qed.
Lemma lem6905932 (h1 : term8) : False.
Proof. exact (EQ_MP (@lem6905931 h1) (@lem6904646 h1)). Qed.
Lemma lem6905933 : term7.
Proof. exact (fun h0 : term8 => @lem6905932 h0). Qed.
Lemma lem6905934 : term6.
Proof. exact (EQ_MP (@lem6904645) (@lem6905933)). Qed.
Lemma lem6905935 : term255 = term4.
Proof. exact (@lem6904641 (@lem6905934)). Qed.
