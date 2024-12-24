Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_MUL_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LT_LMUL_EQ_spec.
Require Import REAL_LT_RMUL_EQ_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1606649 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1606650 : term1 = term2.
Proof. exact (@lem1606649 term1). Qed.
Lemma lem1606651 : term2 = term1.
Proof. exact (SYM (@lem1606650)). Qed.
Lemma lem1606652 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1606655 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1606656 : term5.
Proof. exact (fun h0 : term4 => @lem1606655 h0). Qed.
Lemma lem1606657 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1606658 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1606659 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1606657 h2 (@lem1606658 h1)). Qed.
Lemma lem1606660 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1606659 h1 h0). Qed.
Lemma lem1606661 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1606662 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1606660 h1 (@lem1606661 h2)). Qed.
Lemma lem1606663 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1606662 h0 h1). Qed.
Lemma lem1606664 : term7.
Proof. exact (fun h0 : term5 => @lem1606663 h0). Qed.
Lemma lem1606667 : term5.
Proof. exact (@lem1606664 (@lem1606656)). Qed.
Lemma lem1606721 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1606722 : term8 = term9.
Proof. exact (@lem1606721 term10). Qed.
Lemma lem1606737 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1606738 : term12 = term13.
Proof. exact (MK_COMB (@lem1606737) (@lem1606722)). Qed.
Lemma lem1606741 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1606742 : term15 = term16.
Proof. exact (MK_COMB (@lem1606741) (@lem1606738)). Qed.
Lemma lem1606745 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1606746 : term18 = term19.
Proof. exact (MK_COMB (@lem1606745) (@lem1606742)). Qed.
Lemma lem1606749 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1606756 : term4 = term21.
Proof. exact (MK_COMB (@lem1606749) (@lem1606746)). Qed.
Lemma lem1606765 (z : real) (x : real) (y : real) : (term22 z x y) = (term22 z x y).
Proof. exact (eq_refl (term22 z x y)). Qed.
Lemma lem1606766 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (fun_ext (fun z : real => @lem1606765 z x y)). Qed.
Lemma lem1606767 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606768 (x : real) (y : real) : (term24 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1606767) (@lem1606766 x y)). Qed.
Lemma lem1606769 (x : real) : (term25 x) = (term25 x).
Proof. exact (fun_ext (fun y : real => @lem1606768 x y)). Qed.
Lemma lem1606770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606771 (x : real) : (term26 x) = (term26 x).
Proof. exact (MK_COMB (@lem1606770) (@lem1606769 x)). Qed.
Lemma lem1606772 : term27 = term27.
Proof. exact (fun_ext (fun x : real => @lem1606771 x)). Qed.
Lemma lem1606773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606774 : term10 = term10.
Proof. exact (MK_COMB (@lem1606773) (@lem1606772)). Qed.
Lemma lem1606775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1606776 : term9 = term9.
Proof. exact (MK_COMB (@lem1606775) (@lem1606774)). Qed.
Lemma lem1606785 (z : real) (x : real) (y : real) : (term28 z x y) = (term28 z x y).
Proof. exact (eq_refl (term28 z x y)). Qed.
Lemma lem1606786 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (fun_ext (fun z : real => @lem1606785 z x y)). Qed.
Lemma lem1606787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606788 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1606787) (@lem1606786 x y)). Qed.
Lemma lem1606789 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1606788 x y)). Qed.
Lemma lem1606790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606791 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1606790) (@lem1606789 x)). Qed.
Lemma lem1606792 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1606791 x)). Qed.
Lemma lem1606793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606794 : term34 = term34.
Proof. exact (MK_COMB (@lem1606793) (@lem1606792)). Qed.
Lemma lem1606795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606796 : term11 = term11.
Proof. exact (MK_COMB (@lem1606795) (@lem1606794)). Qed.
Lemma lem1606797 : term13 = term13.
Proof. exact (MK_COMB (@lem1606796) (@lem1606776)). Qed.
Lemma lem1606798 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1606799 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1606798 x)). Qed.
Lemma lem1606800 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606801 : term38 = term38.
Proof. exact (MK_COMB (@lem1606800) (@lem1606799)). Qed.
Lemma lem1606802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606803 : term14 = term14.
Proof. exact (MK_COMB (@lem1606802) (@lem1606801)). Qed.
Lemma lem1606804 : term16 = term16.
Proof. exact (MK_COMB (@lem1606803) (@lem1606797)). Qed.
Lemma lem1606805 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1606806 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1606805 x)). Qed.
Lemma lem1606807 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606808 : term41 = term41.
Proof. exact (MK_COMB (@lem1606807) (@lem1606806)). Qed.
Lemma lem1606809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606810 : term17 = term17.
Proof. exact (MK_COMB (@lem1606809) (@lem1606808)). Qed.
Lemma lem1606811 : term19 = term19.
Proof. exact (MK_COMB (@lem1606810) (@lem1606804)). Qed.
Lemma lem1606820 (y : real) (x : real) : (term42 y x) = (term42 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem1606821 (x : real) : (term43 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1606820 y x)). Qed.
Lemma lem1606822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606823 (x : real) : (term44 x) = (term44 x).
Proof. exact (MK_COMB (@lem1606822) (@lem1606821 x)). Qed.
Lemma lem1606824 : term45 = term45.
Proof. exact (fun_ext (fun x : real => @lem1606823 x)). Qed.
Lemma lem1606825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606826 : term46 = term46.
Proof. exact (MK_COMB (@lem1606825) (@lem1606824)). Qed.
Lemma lem1606835 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1606836 (x : real) : (term48 x) = (term48 x).
Proof. exact (fun_ext (fun y : real => @lem1606835 x y)). Qed.
Lemma lem1606837 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606838 (x : real) : (term49 x) = (term49 x).
Proof. exact (MK_COMB (@lem1606837) (@lem1606836 x)). Qed.
Lemma lem1606839 : term50 = term50.
Proof. exact (fun_ext (fun x : real => @lem1606838 x)). Qed.
Lemma lem1606840 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1606841 : term51 = term51.
Proof. exact (MK_COMB (@lem1606840) (@lem1606839)). Qed.
Lemma lem1606842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606843 : term52 = term52.
Proof. exact (MK_COMB (@lem1606842) (@lem1606841)). Qed.
Lemma lem1606844 : term1 = term1.
Proof. exact (MK_COMB (@lem1606843) (@lem1606826)). Qed.
Lemma lem1606845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1606846 : term3 = term3.
Proof. exact (MK_COMB (@lem1606845) (@lem1606844)). Qed.
Lemma lem1606847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606848 : term20 = term20.
Proof. exact (MK_COMB (@lem1606847) (@lem1606846)). Qed.
Lemma lem1606849 : term21 = term21.
Proof. exact (MK_COMB (@lem1606848) (@lem1606811)). Qed.
Lemma lem1606942 : term4 = term21.
Proof. exact (TRANS (@lem1606756) (@lem1606849)). Qed.
Lemma lem1606943 : term21 = term4.
Proof. exact (SYM (@lem1606942)). Qed.
Lemma lem1606944 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1606945 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1606946 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1606947 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1606948 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1606964 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem17646 (term55 x y) (term56 y)). Qed.
Lemma lem1606966 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1606967 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1606966 x) (@lem1606964 x y)). Qed.
Lemma lem1606968 (x : real) (y : real) : (term60 x y) = (term58 x y).
Proof. exact (@lem17362 (term56 x) ((term55 x y) = (term56 y))). Qed.
Lemma lem1606969 (x : real) (y : real) : (term60 x y) = (term59 x y).
Proof. exact (TRANS (@lem1606968 x y) (@lem1606967 x y)). Qed.
Lemma lem1606970 (P : real -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1606971 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1606970 (term48 x)). Qed.
Lemma lem1606972 (x : real) (y : real) : (term65 x y) = (term47 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1606973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1606974 (x : real) (y : real) : (term66 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1606973) (@lem1606972 x y)). Qed.
Lemma lem1606975 (x : real) (y : real) : (term66 x y) = (term59 x y).
Proof. exact (TRANS (@lem1606974 x y) (@lem1606969 x y)). Qed.
Lemma lem1606976 (x : real) : (term67 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1606975 x y)). Qed.
Lemma lem1606977 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1606978 (x : real) : (term64 x) = (term69 x).
Proof. exact (MK_COMB (@lem1606977) (@lem1606976 x)). Qed.
Lemma lem1606979 (x : real) : (term63 x) = (term69 x).
Proof. exact (TRANS (@lem1606971 x) (@lem1606978 x)). Qed.
Lemma lem1606980 (P : real -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1606981 : term70 = term71.
Proof. exact (@lem1606980 term50). Qed.
Lemma lem1606982 (x : real) : (term72 x) = (term49 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1606983 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1606984 (x : real) : (term73 x) = (term63 x).
Proof. exact (MK_COMB (@lem1606983) (@lem1606982 x)). Qed.
Lemma lem1606985 (x : real) : (term73 x) = (term69 x).
Proof. exact (TRANS (@lem1606984 x) (@lem1606979 x)). Qed.
Lemma lem1606986 : term74 = term75.
Proof. exact (fun_ext (fun x : real => @lem1606985 x)). Qed.
Lemma lem1606987 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1606988 : term71 = term76.
Proof. exact (MK_COMB (@lem1606987) (@lem1606986)). Qed.
Lemma lem1606989 : term70 = term76.
Proof. exact (TRANS (@lem1606981) (@lem1606988)). Qed.
Lemma lem1607005 (y : real) (x : real) : (term77 y x) = (term78 y x).
Proof. exact (@lem17646 (term55 x y) (term56 x)). Qed.
Lemma lem1607007 (y : real) : (term57 y) = (term57 y).
Proof. exact (eq_refl (term57 y)). Qed.
Lemma lem1607008 (y : real) (x : real) : (term79 y x) = (term80 y x).
Proof. exact (MK_COMB (@lem1607007 y) (@lem1607005 y x)). Qed.
Lemma lem1607009 (y : real) (x : real) : (term81 y x) = (term79 y x).
Proof. exact (@lem17362 (term56 y) ((term55 x y) = (term56 x))). Qed.
Lemma lem1607010 (y : real) (x : real) : (term81 y x) = (term80 y x).
Proof. exact (TRANS (@lem1607009 y x) (@lem1607008 y x)). Qed.
Lemma lem1607011 (P : real -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1607012 (x : real) : (term82 x) = (term83 x).
Proof. exact (@lem1607011 (term43 x)). Qed.
Lemma lem1607013 (y : real) (x : real) : (term84 x y) = (term42 y x).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1607014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1607015 (y : real) (x : real) : (term85 x y) = (term81 y x).
Proof. exact (MK_COMB (@lem1607014) (@lem1607013 y x)). Qed.
Lemma lem1607016 (y : real) (x : real) : (term85 x y) = (term80 y x).
Proof. exact (TRANS (@lem1607015 y x) (@lem1607010 y x)). Qed.
Lemma lem1607017 (x : real) : (term86 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1607016 y x)). Qed.
Lemma lem1607018 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607019 (x : real) : (term83 x) = (term88 x).
Proof. exact (MK_COMB (@lem1607018) (@lem1607017 x)). Qed.
Lemma lem1607020 (x : real) : (term82 x) = (term88 x).
Proof. exact (TRANS (@lem1607012 x) (@lem1607019 x)). Qed.
Lemma lem1607021 (P : real -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1607022 : term89 = term90.
Proof. exact (@lem1607021 term45). Qed.
Lemma lem1607023 (x : real) : (term91 x) = (term44 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1607024 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1607025 (x : real) : (term92 x) = (term82 x).
Proof. exact (MK_COMB (@lem1607024) (@lem1607023 x)). Qed.
Lemma lem1607026 (x : real) : (term92 x) = (term88 x).
Proof. exact (TRANS (@lem1607025 x) (@lem1607020 x)). Qed.
Lemma lem1607027 : term93 = term94.
Proof. exact (fun_ext (fun x : real => @lem1607026 x)). Qed.
Lemma lem1607028 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607029 : term90 = term95.
Proof. exact (MK_COMB (@lem1607028) (@lem1607027)). Qed.
Lemma lem1607030 : term89 = term95.
Proof. exact (TRANS (@lem1607022) (@lem1607029)). Qed.
Lemma lem1607031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607032 : term96 = term97.
Proof. exact (MK_COMB (@lem1607031) (@lem1606989)). Qed.
Lemma lem1607033 : term98 = term99.
Proof. exact (MK_COMB (@lem1607032) (@lem1607030)). Qed.
Lemma lem1607034 : term3 = term98.
Proof. exact (@lem17045 term51 term46). Qed.
Lemma lem1607035 : term3 = term99.
Proof. exact (TRANS (@lem1607034) (@lem1607033)). Qed.
Lemma lem1607041 {A : Type'} (P : Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1607042 (P : Prop) (Q : real -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem1607041 real P Q). Qed.
Lemma lem1607043 (x : real) : (term104 x) = (term105 x).
Proof. exact (@lem1607042 (term56 x) (term106 x)). Qed.
Lemma lem1607044 (x : real) (y : real) : (term107 x y) = (term54 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1607045 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1607046 (x : real) (y : real) : (term108 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1607045 x) (@lem1607044 x y)). Qed.
Lemma lem1607047 (x : real) : (term109 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1607046 x y)). Qed.
Lemma lem1607048 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607049 (x : real) : (term104 x) = (term69 x).
Proof. exact (MK_COMB (@lem1607048) (@lem1607047 x)). Qed.
Lemma lem1607050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1607051 (x : real) : (term110 x) = (term111 x).
Proof. exact (MK_COMB (@lem1607050) (@lem1607049 x)). Qed.
Lemma lem1607052 (x : real) (y : real) : (term107 x y) = (term54 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1607053 (x : real) : (term112 x) = (term106 x).
Proof. exact (fun_ext (fun y : real => @lem1607052 x y)). Qed.
Lemma lem1607054 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607055 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1607054) (@lem1607053 x)). Qed.
Lemma lem1607056 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1607057 (x : real) : (term105 x) = (term115 x).
Proof. exact (MK_COMB (@lem1607056 x) (@lem1607055 x)). Qed.
Lemma lem1607058 (x : real) : ((term104 x) = (term105 x)) = ((term69 x) = (term115 x)).
Proof. exact (MK_COMB (@lem1607051 x) (@lem1607057 x)). Qed.
Lemma lem1607059 (x : real) : (term69 x) = (term115 x).
Proof. exact (EQ_MP (@lem1607058 x) (@lem1607043 x)). Qed.
Lemma lem1607061 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1607062 (P : real -> Prop) (Q : real -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem1607061 real P Q). Qed.
Lemma lem1607063 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1607062 (term122 x) (term123 x)). Qed.
Lemma lem1607064 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem1607065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607066 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (MK_COMB (@lem1607065) (@lem1607064 x y)). Qed.
Lemma lem1607067 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (eq_refl (term128 x y)). Qed.
Lemma lem1607068 (x : real) (y : real) : (term130 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1607066 x y) (@lem1607067 x y)). Qed.
Lemma lem1607069 (x : real) : (term131 x) = (term106 x).
Proof. exact (fun_ext (fun y : real => @lem1607068 x y)). Qed.
Lemma lem1607070 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607071 (x : real) : (term120 x) = (term114 x).
Proof. exact (MK_COMB (@lem1607070) (@lem1607069 x)). Qed.
Lemma lem1607072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1607073 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1607072) (@lem1607071 x)). Qed.
Lemma lem1607074 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem1607075 (x : real) : (term134 x) = (term122 x).
Proof. exact (fun_ext (fun y : real => @lem1607074 x y)). Qed.
Lemma lem1607076 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607077 (x : real) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1607076) (@lem1607075 x)). Qed.
Lemma lem1607078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607079 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1607078) (@lem1607077 x)). Qed.
Lemma lem1607080 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (eq_refl (term128 x y)). Qed.
Lemma lem1607081 (x : real) : (term139 x) = (term123 x).
Proof. exact (fun_ext (fun y : real => @lem1607080 x y)). Qed.
Lemma lem1607082 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607083 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1607082) (@lem1607081 x)). Qed.
Lemma lem1607084 (x : real) : (term121 x) = (term142 x).
Proof. exact (MK_COMB (@lem1607079 x) (@lem1607083 x)). Qed.
Lemma lem1607085 (x : real) : ((term120 x) = (term121 x)) = ((term114 x) = (term142 x)).
Proof. exact (MK_COMB (@lem1607073 x) (@lem1607084 x)). Qed.
Lemma lem1607086 (x : real) : (term114 x) = (term142 x).
Proof. exact (EQ_MP (@lem1607085 x) (@lem1607063 x)). Qed.
Lemma lem1607183 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1607184 (x : real) : (term115 x) = (term143 x).
Proof. exact (MK_COMB (@lem1607183 x) (@lem1607086 x)). Qed.
Lemma lem1607185 (x : real) : (term69 x) = (term143 x).
Proof. exact (TRANS (@lem1607059 x) (@lem1607184 x)). Qed.
Lemma lem1607186 : term75 = term144.
Proof. exact (fun_ext (fun x : real => @lem1607185 x)). Qed.
Lemma lem1607187 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607188 : term76 = term145.
Proof. exact (MK_COMB (@lem1607187) (@lem1607186)). Qed.
Lemma lem1607237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607238 : term97 = term146.
Proof. exact (MK_COMB (@lem1607237) (@lem1607188)). Qed.
Lemma lem1607291 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1607292 : term99 = term147.
Proof. exact (MK_COMB (@lem1607238) (@lem1607291)). Qed.
Lemma lem1607294 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term117 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1607295 (P : real -> Prop) (Q : real -> Prop) : (term119 P Q) = (term118 P Q).
Proof. exact (@lem1607294 real P Q). Qed.
Lemma lem1607296 (x : real) : (term121 x) = (term120 x).
Proof. exact (@lem1607295 (term122 x) (term123 x)). Qed.
Lemma lem1607297 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem1607298 (x : real) : (term134 x) = (term122 x).
Proof. exact (fun_ext (fun y : real => @lem1607297 x y)). Qed.
Lemma lem1607299 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607300 (x : real) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1607299) (@lem1607298 x)). Qed.
Lemma lem1607301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607302 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1607301) (@lem1607300 x)). Qed.
Lemma lem1607303 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (eq_refl (term128 x y)). Qed.
Lemma lem1607304 (x : real) : (term139 x) = (term123 x).
Proof. exact (fun_ext (fun y : real => @lem1607303 x y)). Qed.
Lemma lem1607305 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607306 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1607305) (@lem1607304 x)). Qed.
Lemma lem1607307 (x : real) : (term121 x) = (term142 x).
Proof. exact (MK_COMB (@lem1607302 x) (@lem1607306 x)). Qed.
Lemma lem1607308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1607309 (x : real) : (term148 x) = (term149 x).
Proof. exact (MK_COMB (@lem1607308) (@lem1607307 x)). Qed.
Lemma lem1607310 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem1607311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607312 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (MK_COMB (@lem1607311) (@lem1607310 x y)). Qed.
Lemma lem1607313 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (eq_refl (term128 x y)). Qed.
Lemma lem1607314 (x : real) (y : real) : (term130 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1607312 x y) (@lem1607313 x y)). Qed.
Lemma lem1607315 (x : real) : (term131 x) = (term106 x).
Proof. exact (fun_ext (fun y : real => @lem1607314 x y)). Qed.
Lemma lem1607316 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607317 (x : real) : (term120 x) = (term114 x).
Proof. exact (MK_COMB (@lem1607316) (@lem1607315 x)). Qed.
Lemma lem1607318 (x : real) : ((term121 x) = (term120 x)) = ((term142 x) = (term114 x)).
Proof. exact (MK_COMB (@lem1607309 x) (@lem1607317 x)). Qed.
Lemma lem1607319 (x : real) : (term142 x) = (term114 x).
Proof. exact (EQ_MP (@lem1607318 x) (@lem1607296 x)). Qed.
Lemma lem1607320 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1607321 (x : real) : (term143 x) = (term115 x).
Proof. exact (MK_COMB (@lem1607320 x) (@lem1607319 x)). Qed.
Lemma lem1607323 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1607324 (P : Prop) (Q : real -> Prop) : (term103 P Q) = (term102 P Q).
Proof. exact (@lem1607323 real P Q). Qed.
Lemma lem1607325 (x : real) : (term105 x) = (term104 x).
Proof. exact (@lem1607324 (term56 x) (term106 x)). Qed.
Lemma lem1607326 (x : real) (y : real) : (term107 x y) = (term54 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1607327 (x : real) : (term112 x) = (term106 x).
Proof. exact (fun_ext (fun y : real => @lem1607326 x y)). Qed.
Lemma lem1607328 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607329 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1607328) (@lem1607327 x)). Qed.
Lemma lem1607330 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1607331 (x : real) : (term105 x) = (term115 x).
Proof. exact (MK_COMB (@lem1607330 x) (@lem1607329 x)). Qed.
Lemma lem1607332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1607333 (x : real) : (term150 x) = (term151 x).
Proof. exact (MK_COMB (@lem1607332) (@lem1607331 x)). Qed.
Lemma lem1607334 (x : real) (y : real) : (term107 x y) = (term54 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1607335 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1607336 (x : real) (y : real) : (term108 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1607335 x) (@lem1607334 x y)). Qed.
Lemma lem1607337 (x : real) : (term109 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1607336 x y)). Qed.
Lemma lem1607338 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607339 (x : real) : (term104 x) = (term69 x).
Proof. exact (MK_COMB (@lem1607338) (@lem1607337 x)). Qed.
Lemma lem1607340 (x : real) : ((term105 x) = (term104 x)) = ((term115 x) = (term69 x)).
Proof. exact (MK_COMB (@lem1607333 x) (@lem1607339 x)). Qed.
Lemma lem1607341 (x : real) : (term115 x) = (term69 x).
Proof. exact (EQ_MP (@lem1607340 x) (@lem1607325 x)). Qed.
Lemma lem1607342 (x : real) : (term143 x) = (term69 x).
Proof. exact (TRANS (@lem1607321 x) (@lem1607341 x)). Qed.
Lemma lem1607343 : term144 = term75.
Proof. exact (fun_ext (fun x : real => @lem1607342 x)). Qed.
Lemma lem1607344 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607345 : term145 = term76.
Proof. exact (MK_COMB (@lem1607344) (@lem1607343)). Qed.
Lemma lem1607346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607347 : term146 = term97.
Proof. exact (MK_COMB (@lem1607346) (@lem1607345)). Qed.
Lemma lem1607348 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1607349 : term147 = term99.
Proof. exact (MK_COMB (@lem1607347) (@lem1607348)). Qed.
Lemma lem1607351 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term117 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1607352 (P : real -> Prop) (Q : real -> Prop) : (term119 P Q) = (term118 P Q).
Proof. exact (@lem1607351 real P Q). Qed.
Lemma lem1607353 : term152 = term153.
Proof. exact (@lem1607352 term75 term94). Qed.
Lemma lem1607354 (x : real) : (term154 x) = (term69 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1607355 : term155 = term75.
Proof. exact (fun_ext (fun x : real => @lem1607354 x)). Qed.
Lemma lem1607356 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607357 : term156 = term76.
Proof. exact (MK_COMB (@lem1607356) (@lem1607355)). Qed.
Lemma lem1607358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607359 : term157 = term97.
Proof. exact (MK_COMB (@lem1607358) (@lem1607357)). Qed.
Lemma lem1607360 (x : real) : (term158 x) = (term88 x).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1607361 : term159 = term94.
Proof. exact (fun_ext (fun x : real => @lem1607360 x)). Qed.
Lemma lem1607362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607363 : term160 = term95.
Proof. exact (MK_COMB (@lem1607362) (@lem1607361)). Qed.
Lemma lem1607364 : term152 = term99.
Proof. exact (MK_COMB (@lem1607359) (@lem1607363)). Qed.
Lemma lem1607365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1607366 : term161 = term162.
Proof. exact (MK_COMB (@lem1607365) (@lem1607364)). Qed.
Lemma lem1607367 (x : real) : (term154 x) = (term69 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1607368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607369 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1607368) (@lem1607367 x)). Qed.
Lemma lem1607370 (x : real) : (term158 x) = (term88 x).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1607371 (x : real) : (term165 x) = (term166 x).
Proof. exact (MK_COMB (@lem1607369 x) (@lem1607370 x)). Qed.
Lemma lem1607372 : term167 = term168.
Proof. exact (fun_ext (fun x : real => @lem1607371 x)). Qed.
Lemma lem1607373 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607374 : term153 = term169.
Proof. exact (MK_COMB (@lem1607373) (@lem1607372)). Qed.
Lemma lem1607375 : (term152 = term153) = (term99 = term169).
Proof. exact (MK_COMB (@lem1607366) (@lem1607374)). Qed.
Lemma lem1607376 : term99 = term169.
Proof. exact (EQ_MP (@lem1607375) (@lem1607353)). Qed.
Lemma lem1607378 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term117 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1607379 (P : real -> Prop) (Q : real -> Prop) : (term119 P Q) = (term118 P Q).
Proof. exact (@lem1607378 real P Q). Qed.
Lemma lem1607380 (x : real) : (term170 x) = (term171 x).
Proof. exact (@lem1607379 (term68 x) (term87 x)). Qed.
Lemma lem1607381 (x : real) (y : real) : (term172 x y) = (term59 x y).
Proof. exact (eq_refl (term172 x y)). Qed.
Lemma lem1607382 (x : real) : (term173 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1607381 x y)). Qed.
Lemma lem1607383 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607384 (x : real) : (term174 x) = (term69 x).
Proof. exact (MK_COMB (@lem1607383) (@lem1607382 x)). Qed.
Lemma lem1607385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607386 (x : real) : (term175 x) = (term164 x).
Proof. exact (MK_COMB (@lem1607385) (@lem1607384 x)). Qed.
Lemma lem1607387 (y : real) (x : real) : (term176 x y) = (term80 y x).
Proof. exact (eq_refl (term176 x y)). Qed.
Lemma lem1607388 (x : real) : (term177 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1607387 y x)). Qed.
Lemma lem1607389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607390 (x : real) : (term178 x) = (term88 x).
Proof. exact (MK_COMB (@lem1607389) (@lem1607388 x)). Qed.
Lemma lem1607391 (x : real) : (term170 x) = (term166 x).
Proof. exact (MK_COMB (@lem1607386 x) (@lem1607390 x)). Qed.
Lemma lem1607392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1607393 (x : real) : (term179 x) = (term180 x).
Proof. exact (MK_COMB (@lem1607392) (@lem1607391 x)). Qed.
Lemma lem1607394 (x : real) (y : real) : (term172 x y) = (term59 x y).
Proof. exact (eq_refl (term172 x y)). Qed.
Lemma lem1607395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1607396 (x : real) (y : real) : (term181 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1607395) (@lem1607394 x y)). Qed.
Lemma lem1607397 (y : real) (x : real) : (term176 x y) = (term80 y x).
Proof. exact (eq_refl (term176 x y)). Qed.
Lemma lem1607398 (y : real) (x : real) : (term183 x y) = (term184 y x).
Proof. exact (MK_COMB (@lem1607396 x y) (@lem1607397 y x)). Qed.
Lemma lem1607399 (x : real) : (term185 x) = (term186 x).
Proof. exact (fun_ext (fun y : real => @lem1607398 y x)). Qed.
Lemma lem1607400 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607401 (x : real) : (term171 x) = (term187 x).
Proof. exact (MK_COMB (@lem1607400) (@lem1607399 x)). Qed.
Lemma lem1607402 (x : real) : ((term170 x) = (term171 x)) = ((term166 x) = (term187 x)).
Proof. exact (MK_COMB (@lem1607393 x) (@lem1607401 x)). Qed.
Lemma lem1607403 (x : real) : (term166 x) = (term187 x).
Proof. exact (EQ_MP (@lem1607402 x) (@lem1607380 x)). Qed.
Lemma lem1607404 : term168 = term188.
Proof. exact (fun_ext (fun x : real => @lem1607403 x)). Qed.
Lemma lem1607405 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1607406 : term169 = term189.
Proof. exact (MK_COMB (@lem1607405) (@lem1607404)). Qed.
Lemma lem1607407 : term99 = term189.
Proof. exact (TRANS (@lem1607376) (@lem1607406)). Qed.
Lemma lem1607408 : term147 = term189.
Proof. exact (TRANS (@lem1607349) (@lem1607407)). Qed.
Lemma lem1607409 : term99 = term189.
Proof. exact (TRANS (@lem1607292) (@lem1607408)). Qed.
Lemma lem1607410 : term3 = term189.
Proof. exact (TRANS (@lem1607035) (@lem1607409)). Qed.
Lemma lem1607411 (h1 : term3) : term189.
Proof. exact (EQ_MP (@lem1607410) (@lem1606944 h1)). Qed.
Lemma lem1607412 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1607413 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1607412 x)). Qed.
Lemma lem1607414 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607423 : term41 = term41.
Proof. exact (MK_COMB (@lem1607414) (@lem1607413)). Qed.
Lemma lem1607424 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1607423) (@lem1606945 h1)). Qed.
Lemma lem1607425 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1607426 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1607425 x)). Qed.
Lemma lem1607427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607436 : term38 = term38.
Proof. exact (MK_COMB (@lem1607427) (@lem1607426)). Qed.
Lemma lem1607437 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1607436) (@lem1606946 h1)). Qed.
Lemma lem1607453 (z : real) (x : real) (y : real) : ((term190 x y z) = (real_lt x y)) = (term191 z x y).
Proof. exact (@lem17784 (term190 x y z) (real_lt x y)). Qed.
Lemma lem1607455 (z : real) : (term192 z) = (term192 z).
Proof. exact (eq_refl (term192 z)). Qed.
Lemma lem1607456 (z : real) (x : real) (y : real) : (term193 z x y) = (term194 z x y).
Proof. exact (MK_COMB (@lem1607455 z) (@lem1607453 z x y)). Qed.
Lemma lem1607457 (z : real) (x : real) (y : real) : (term28 z x y) = (term193 z x y).
Proof. exact (@lem17265 (term56 z) ((term190 x y z) = (real_lt x y))). Qed.
Lemma lem1607458 (z : real) (x : real) (y : real) : (term28 z x y) = (term194 z x y).
Proof. exact (TRANS (@lem1607457 z x y) (@lem1607456 z x y)). Qed.
Lemma lem1607459 (x : real) (y : real) : (term29 x y) = (term195 x y).
Proof. exact (fun_ext (fun z : real => @lem1607458 z x y)). Qed.
Lemma lem1607460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607461 (x : real) (y : real) : (term30 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1607460) (@lem1607459 x y)). Qed.
Lemma lem1607462 (x : real) : (term31 x) = (term197 x).
Proof. exact (fun_ext (fun y : real => @lem1607461 x y)). Qed.
Lemma lem1607463 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607464 (x : real) : (term32 x) = (term198 x).
Proof. exact (MK_COMB (@lem1607463) (@lem1607462 x)). Qed.
Lemma lem1607465 : term33 = term199.
Proof. exact (fun_ext (fun x : real => @lem1607464 x)). Qed.
Lemma lem1607466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607527 : term34 = term200.
Proof. exact (MK_COMB (@lem1607466) (@lem1607465)). Qed.
Lemma lem1607528 (h1 : term34) : term200.
Proof. exact (EQ_MP (@lem1607527) (@lem1606947 h1)). Qed.
Lemma lem1607544 (z : real) (x : real) (y : real) : ((term201 x z y) = (real_lt x y)) = (term202 z x y).
Proof. exact (@lem17784 (term201 x z y) (real_lt x y)). Qed.
Lemma lem1607546 (z : real) : (term192 z) = (term192 z).
Proof. exact (eq_refl (term192 z)). Qed.
Lemma lem1607547 (z : real) (x : real) (y : real) : (term203 z x y) = (term204 z x y).
Proof. exact (MK_COMB (@lem1607546 z) (@lem1607544 z x y)). Qed.
Lemma lem1607548 (z : real) (x : real) (y : real) : (term22 z x y) = (term203 z x y).
Proof. exact (@lem17265 (term56 z) ((term201 x z y) = (real_lt x y))). Qed.
Lemma lem1607549 (z : real) (x : real) (y : real) : (term22 z x y) = (term204 z x y).
Proof. exact (TRANS (@lem1607548 z x y) (@lem1607547 z x y)). Qed.
Lemma lem1607550 (x : real) (y : real) : (term23 x y) = (term205 x y).
Proof. exact (fun_ext (fun z : real => @lem1607549 z x y)). Qed.
Lemma lem1607551 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607552 (x : real) (y : real) : (term24 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1607551) (@lem1607550 x y)). Qed.
Lemma lem1607553 (x : real) : (term25 x) = (term207 x).
Proof. exact (fun_ext (fun y : real => @lem1607552 x y)). Qed.
Lemma lem1607554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607555 (x : real) : (term26 x) = (term208 x).
Proof. exact (MK_COMB (@lem1607554) (@lem1607553 x)). Qed.
Lemma lem1607556 : term27 = term209.
Proof. exact (fun_ext (fun x : real => @lem1607555 x)). Qed.
Lemma lem1607557 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607618 : term10 = term210.
Proof. exact (MK_COMB (@lem1607557) (@lem1607556)). Qed.
Lemma lem1607619 (h1 : term10) : term210.
Proof. exact (EQ_MP (@lem1607618) (@lem1606948 h1)). Qed.
Lemma lem1607620 (x : real) (h1 : term187 x) : term187 x.
Proof. exact (h1). Qed.
Lemma lem1607638 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1607639 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1607638 x)). Qed.
Lemma lem1607640 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607641 : term41 = term41.
Proof. exact (MK_COMB (@lem1607640) (@lem1607639)). Qed.
Lemma lem1607642 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1607641) (@lem1607424 h1)). Qed.
Lemma lem1607659 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1607660 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1607659 x)). Qed.
Lemma lem1607661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607662 : term38 = term38.
Proof. exact (MK_COMB (@lem1607661) (@lem1607660)). Qed.
Lemma lem1607663 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1607662) (@lem1607437 h1)). Qed.
Lemma lem1607726 (z : real) (x : real) (y : real) : (term194 z x y) = (term194 z x y).
Proof. exact (eq_refl (term194 z x y)). Qed.
Lemma lem1607727 (x : real) (y : real) : (term195 x y) = (term195 x y).
Proof. exact (fun_ext (fun z : real => @lem1607726 z x y)). Qed.
Lemma lem1607728 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607729 (x : real) (y : real) : (term196 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1607728) (@lem1607727 x y)). Qed.
Lemma lem1607730 (x : real) : (term197 x) = (term197 x).
Proof. exact (fun_ext (fun y : real => @lem1607729 x y)). Qed.
Lemma lem1607731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607732 (x : real) : (term198 x) = (term198 x).
Proof. exact (MK_COMB (@lem1607731) (@lem1607730 x)). Qed.
Lemma lem1607733 : term199 = term199.
Proof. exact (fun_ext (fun x : real => @lem1607732 x)). Qed.
Lemma lem1607734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607735 : term200 = term200.
Proof. exact (MK_COMB (@lem1607734) (@lem1607733)). Qed.
Lemma lem1607736 (h1 : term34) : term200.
Proof. exact (EQ_MP (@lem1607735) (@lem1607528 h1)). Qed.
Lemma lem1607799 (z : real) (x : real) (y : real) : (term204 z x y) = (term204 z x y).
Proof. exact (eq_refl (term204 z x y)). Qed.
Lemma lem1607800 (x : real) (y : real) : (term205 x y) = (term205 x y).
Proof. exact (fun_ext (fun z : real => @lem1607799 z x y)). Qed.
Lemma lem1607801 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607802 (x : real) (y : real) : (term206 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1607801) (@lem1607800 x y)). Qed.
Lemma lem1607803 (x : real) : (term207 x) = (term207 x).
Proof. exact (fun_ext (fun y : real => @lem1607802 x y)). Qed.
Lemma lem1607804 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607805 (x : real) : (term208 x) = (term208 x).
Proof. exact (MK_COMB (@lem1607804) (@lem1607803 x)). Qed.
Lemma lem1607806 : term209 = term209.
Proof. exact (fun_ext (fun x : real => @lem1607805 x)). Qed.
Lemma lem1607807 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607808 : term210 = term210.
Proof. exact (MK_COMB (@lem1607807) (@lem1607806)). Qed.
Lemma lem1607809 (h1 : term10) : term210.
Proof. exact (EQ_MP (@lem1607808) (@lem1607619 h1)). Qed.
Lemma lem1607951 (y : real) (x : real) (h1 : term184 y x) : term184 y x.
Proof. exact (h1). Qed.
Lemma lem1607952 (x : real) (y : real) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem1607953 (y : real) (x : real) (h1 : term80 y x) : term80 y x.
Proof. exact (h1). Qed.
Lemma lem1607954 (x : real) (y : real) (h1 : term59 x y) : term54 x y.
Proof. exact (proj2 (@lem1607952 x y h1)). Qed.
Lemma lem1607956 (x : real) (y : real) (h1 : term125 x y) : term125 x y.
Proof. exact (h1). Qed.
Lemma lem1607957 (x : real) (y : real) (h1 : term129 x y) : term129 x y.
Proof. exact (h1). Qed.
Lemma lem1607962 (y : real) (x : real) (h1 : term80 y x) : term78 y x.
Proof. exact (proj2 (@lem1607953 y x h1)). Qed.
Lemma lem1607964 (y : real) (x : real) (h1 : term211 y x) : term211 y x.
Proof. exact (h1). Qed.
Lemma lem1607965 (y : real) (x : real) (h1 : term212 y x) : term212 y x.
Proof. exact (h1). Qed.
Lemma lem1607971 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1607972 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1607971 x)). Qed.
Lemma lem1607973 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1607975 : term41 = term41.
Proof. exact (MK_COMB (@lem1607973) (@lem1607972)). Qed.
Lemma lem1607976 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1607975) (@lem1607642 h1)). Qed.
Lemma lem1608054 (z : real) (x : real) (y : real) : (term204 z x y) = (term213 z x y).
Proof. exact (@lem19490 (term214 z x y) (term215 z) (term216 z x y)). Qed.
Lemma lem1608055 (x : real) (y : real) : (term205 x y) = (term217 x y).
Proof. exact (fun_ext (fun z : real => @lem1608054 z x y)). Qed.
Lemma lem1608056 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608057 (x : real) (y : real) : (term206 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1608056) (@lem1608055 x y)). Qed.
Lemma lem1608058 (x : real) : (term207 x) = (term219 x).
Proof. exact (fun_ext (fun y : real => @lem1608057 x y)). Qed.
Lemma lem1608059 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608060 (x : real) : (term208 x) = (term220 x).
Proof. exact (MK_COMB (@lem1608059) (@lem1608058 x)). Qed.
Lemma lem1608061 : term209 = term221.
Proof. exact (fun_ext (fun x : real => @lem1608060 x)). Qed.
Lemma lem1608062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608064 : term210 = term222.
Proof. exact (MK_COMB (@lem1608062) (@lem1608061)). Qed.
Lemma lem1608065 (h1 : term10) : term222.
Proof. exact (EQ_MP (@lem1608064) (@lem1607809 h1)). Qed.
Lemma lem1608086 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1608087 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1608086 x)). Qed.
Lemma lem1608088 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608090 : term38 = term38.
Proof. exact (MK_COMB (@lem1608088) (@lem1608087)). Qed.
Lemma lem1608091 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1608090) (@lem1607663 h1)). Qed.
Lemma lem1608121 (z : real) (x : real) (y : real) : (term194 z x y) = (term223 z x y).
Proof. exact (@lem19490 (term224 z x y) (term215 z) (term225 z x y)). Qed.
Lemma lem1608122 (x : real) (y : real) : (term195 x y) = (term226 x y).
Proof. exact (fun_ext (fun z : real => @lem1608121 z x y)). Qed.
Lemma lem1608123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608124 (x : real) (y : real) : (term196 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1608123) (@lem1608122 x y)). Qed.
Lemma lem1608125 (x : real) : (term197 x) = (term228 x).
Proof. exact (fun_ext (fun y : real => @lem1608124 x y)). Qed.
Lemma lem1608126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608127 (x : real) : (term198 x) = (term229 x).
Proof. exact (MK_COMB (@lem1608126) (@lem1608125 x)). Qed.
Lemma lem1608128 : term199 = term230.
Proof. exact (fun_ext (fun x : real => @lem1608127 x)). Qed.
Lemma lem1608129 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608131 : term200 = term231.
Proof. exact (MK_COMB (@lem1608129) (@lem1608128)). Qed.
Lemma lem1608132 (h1 : term34) : term231.
Proof. exact (EQ_MP (@lem1608131) (@lem1607736 h1)). Qed.
Lemma lem1608194 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1608195 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1608194 x)). Qed.
Lemma lem1608196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608198 : term38 = term38.
Proof. exact (MK_COMB (@lem1608196) (@lem1608195)). Qed.
Lemma lem1608199 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1608198) (@lem1607663 h1)). Qed.
Lemma lem1608229 (z : real) (x : real) (y : real) : (term194 z x y) = (term223 z x y).
Proof. exact (@lem19490 (term224 z x y) (term215 z) (term225 z x y)). Qed.
Lemma lem1608230 (x : real) (y : real) : (term195 x y) = (term226 x y).
Proof. exact (fun_ext (fun z : real => @lem1608229 z x y)). Qed.
Lemma lem1608231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608232 (x : real) (y : real) : (term196 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1608231) (@lem1608230 x y)). Qed.
Lemma lem1608233 (x : real) : (term197 x) = (term228 x).
Proof. exact (fun_ext (fun y : real => @lem1608232 x y)). Qed.
Lemma lem1608234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608235 (x : real) : (term198 x) = (term229 x).
Proof. exact (MK_COMB (@lem1608234) (@lem1608233 x)). Qed.
Lemma lem1608236 : term199 = term230.
Proof. exact (fun_ext (fun x : real => @lem1608235 x)). Qed.
Lemma lem1608237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608239 : term200 = term231.
Proof. exact (MK_COMB (@lem1608237) (@lem1608236)). Qed.
Lemma lem1608240 (h1 : term34) : term231.
Proof. exact (EQ_MP (@lem1608239) (@lem1607736 h1)). Qed.
Lemma lem1608302 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1608303 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1608302 x)). Qed.
Lemma lem1608304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608306 : term38 = term38.
Proof. exact (MK_COMB (@lem1608304) (@lem1608303)). Qed.
Lemma lem1608307 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1608306) (@lem1607663 h1)). Qed.
Lemma lem1608337 (z : real) (x : real) (y : real) : (term194 z x y) = (term223 z x y).
Proof. exact (@lem19490 (term224 z x y) (term215 z) (term225 z x y)). Qed.
Lemma lem1608338 (x : real) (y : real) : (term195 x y) = (term226 x y).
Proof. exact (fun_ext (fun z : real => @lem1608337 z x y)). Qed.
Lemma lem1608339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608340 (x : real) (y : real) : (term196 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1608339) (@lem1608338 x y)). Qed.
Lemma lem1608341 (x : real) : (term197 x) = (term228 x).
Proof. exact (fun_ext (fun y : real => @lem1608340 x y)). Qed.
Lemma lem1608342 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608343 (x : real) : (term198 x) = (term229 x).
Proof. exact (MK_COMB (@lem1608342) (@lem1608341 x)). Qed.
Lemma lem1608344 : term199 = term230.
Proof. exact (fun_ext (fun x : real => @lem1608343 x)). Qed.
Lemma lem1608345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1608347 : term200 = term231.
Proof. exact (MK_COMB (@lem1608345) (@lem1608344)). Qed.
Lemma lem1608348 (h1 : term34) : term231.
Proof. exact (EQ_MP (@lem1608347) (@lem1607736 h1)). Qed.
Lemma lem1608402 (_25389 : real) (h1 : term41) : term232 _25389.
Proof. exact (@lem1607976 h1 _25389). Qed.
Lemma lem1608403 (_25389 : real) : (term232 _25389) = ((term39 _25389) = term36).
Proof. exact (eq_refl (term232 _25389)). Qed.
Lemma lem1608417 (_25394 : real) (h1 : term10) : term233 _25394.
Proof. exact (@lem1608065 h1 _25394). Qed.
Lemma lem1608418 (_25394 : real) : (term233 _25394) = (term220 _25394).
Proof. exact (eq_refl (term233 _25394)). Qed.
Lemma lem1608419 (_25394 : real) (h1 : term10) : term220 _25394.
Proof. exact (EQ_MP (@lem1608418 _25394) (@lem1608417 _25394 h1)). Qed.
Lemma lem1608420 (_25394 : real) (_25395 : real) (h1 : term10) : term234 _25394 _25395.
Proof. exact (@lem1608419 _25394 h1 _25395). Qed.
Lemma lem1608421 (_25394 : real) (_25395 : real) : (term234 _25394 _25395) = (term218 _25394 _25395).
Proof. exact (eq_refl (term234 _25394 _25395)). Qed.
Lemma lem1608422 (_25394 : real) (_25395 : real) (h1 : term10) : term218 _25394 _25395.
Proof. exact (EQ_MP (@lem1608421 _25394 _25395) (@lem1608420 _25394 _25395 h1)). Qed.
Lemma lem1608423 (_25394 : real) (_25395 : real) (_25396 : real) (h1 : term10) : term235 _25394 _25395 _25396.
Proof. exact (@lem1608422 _25394 _25395 h1 _25396). Qed.
Lemma lem1608424 (_25396 : real) (_25394 : real) (_25395 : real) : (term235 _25394 _25395 _25396) = (term213 _25396 _25394 _25395).
Proof. exact (eq_refl (term235 _25394 _25395 _25396)). Qed.
Lemma lem1608425 (_25396 : real) (_25394 : real) (_25395 : real) (h1 : term10) : term213 _25396 _25394 _25395.
Proof. exact (EQ_MP (@lem1608424 _25396 _25394 _25395) (@lem1608423 _25394 _25395 _25396 h1)). Qed.
Lemma lem1608429 (_25398 : real) (h1 : term38) : term236 _25398.
Proof. exact (@lem1608091 h1 _25398). Qed.
Lemma lem1608430 (_25398 : real) : (term236 _25398) = ((term35 _25398) = term36).
Proof. exact (eq_refl (term236 _25398)). Qed.
Lemma lem1608432 (_25399 : real) (h1 : term34) : term237 _25399.
Proof. exact (@lem1608132 h1 _25399). Qed.
Lemma lem1608433 (_25399 : real) : (term237 _25399) = (term229 _25399).
Proof. exact (eq_refl (term237 _25399)). Qed.
Lemma lem1608434 (_25399 : real) (h1 : term34) : term229 _25399.
Proof. exact (EQ_MP (@lem1608433 _25399) (@lem1608432 _25399 h1)). Qed.
Lemma lem1608435 (_25399 : real) (_25400 : real) (h1 : term34) : term238 _25399 _25400.
Proof. exact (@lem1608434 _25399 h1 _25400). Qed.
Lemma lem1608436 (_25399 : real) (_25400 : real) : (term238 _25399 _25400) = (term227 _25399 _25400).
Proof. exact (eq_refl (term238 _25399 _25400)). Qed.
Lemma lem1608437 (_25399 : real) (_25400 : real) (h1 : term34) : term227 _25399 _25400.
Proof. exact (EQ_MP (@lem1608436 _25399 _25400) (@lem1608435 _25399 _25400 h1)). Qed.
Lemma lem1608438 (_25399 : real) (_25400 : real) (_25401 : real) (h1 : term34) : term239 _25399 _25400 _25401.
Proof. exact (@lem1608437 _25399 _25400 h1 _25401). Qed.
Lemma lem1608439 (_25401 : real) (_25399 : real) (_25400 : real) : (term239 _25399 _25400 _25401) = (term223 _25401 _25399 _25400).
Proof. exact (eq_refl (term239 _25399 _25400 _25401)). Qed.
Lemma lem1608440 (_25401 : real) (_25399 : real) (_25400 : real) (h1 : term34) : term223 _25401 _25399 _25400.
Proof. exact (EQ_MP (@lem1608439 _25401 _25399 _25400) (@lem1608438 _25399 _25400 _25401 h1)). Qed.
Lemma lem1608453 (_25406 : real) (h1 : term38) : term236 _25406.
Proof. exact (@lem1608199 h1 _25406). Qed.
Lemma lem1608454 (_25406 : real) : (term236 _25406) = ((term35 _25406) = term36).
Proof. exact (eq_refl (term236 _25406)). Qed.
Lemma lem1608456 (_25407 : real) (h1 : term34) : term237 _25407.
Proof. exact (@lem1608240 h1 _25407). Qed.
Lemma lem1608457 (_25407 : real) : (term237 _25407) = (term229 _25407).
Proof. exact (eq_refl (term237 _25407)). Qed.
Lemma lem1608458 (_25407 : real) (h1 : term34) : term229 _25407.
Proof. exact (EQ_MP (@lem1608457 _25407) (@lem1608456 _25407 h1)). Qed.
Lemma lem1608459 (_25407 : real) (_25408 : real) (h1 : term34) : term238 _25407 _25408.
Proof. exact (@lem1608458 _25407 h1 _25408). Qed.
Lemma lem1608460 (_25407 : real) (_25408 : real) : (term238 _25407 _25408) = (term227 _25407 _25408).
Proof. exact (eq_refl (term238 _25407 _25408)). Qed.
Lemma lem1608461 (_25407 : real) (_25408 : real) (h1 : term34) : term227 _25407 _25408.
Proof. exact (EQ_MP (@lem1608460 _25407 _25408) (@lem1608459 _25407 _25408 h1)). Qed.
Lemma lem1608462 (_25407 : real) (_25408 : real) (_25409 : real) (h1 : term34) : term239 _25407 _25408 _25409.
Proof. exact (@lem1608461 _25407 _25408 h1 _25409). Qed.
Lemma lem1608463 (_25409 : real) (_25407 : real) (_25408 : real) : (term239 _25407 _25408 _25409) = (term223 _25409 _25407 _25408).
Proof. exact (eq_refl (term239 _25407 _25408 _25409)). Qed.
Lemma lem1608464 (_25409 : real) (_25407 : real) (_25408 : real) (h1 : term34) : term223 _25409 _25407 _25408.
Proof. exact (EQ_MP (@lem1608463 _25409 _25407 _25408) (@lem1608462 _25407 _25408 _25409 h1)). Qed.
Lemma lem1608477 (_25414 : real) (h1 : term38) : term236 _25414.
Proof. exact (@lem1608307 h1 _25414). Qed.
Lemma lem1608478 (_25414 : real) : (term236 _25414) = ((term35 _25414) = term36).
Proof. exact (eq_refl (term236 _25414)). Qed.
Lemma lem1608480 (_25415 : real) (h1 : term34) : term237 _25415.
Proof. exact (@lem1608348 h1 _25415). Qed.
Lemma lem1608481 (_25415 : real) : (term237 _25415) = (term229 _25415).
Proof. exact (eq_refl (term237 _25415)). Qed.
Lemma lem1608482 (_25415 : real) (h1 : term34) : term229 _25415.
Proof. exact (EQ_MP (@lem1608481 _25415) (@lem1608480 _25415 h1)). Qed.
Lemma lem1608483 (_25415 : real) (_25416 : real) (h1 : term34) : term238 _25415 _25416.
Proof. exact (@lem1608482 _25415 h1 _25416). Qed.
Lemma lem1608484 (_25415 : real) (_25416 : real) : (term238 _25415 _25416) = (term227 _25415 _25416).
Proof. exact (eq_refl (term238 _25415 _25416)). Qed.
Lemma lem1608485 (_25415 : real) (_25416 : real) (h1 : term34) : term227 _25415 _25416.
Proof. exact (EQ_MP (@lem1608484 _25415 _25416) (@lem1608483 _25415 _25416 h1)). Qed.
Lemma lem1608486 (_25415 : real) (_25416 : real) (_25417 : real) (h1 : term34) : term239 _25415 _25416 _25417.
Proof. exact (@lem1608485 _25415 _25416 h1 _25417). Qed.
Lemma lem1608487 (_25417 : real) (_25415 : real) (_25416 : real) : (term239 _25415 _25416 _25417) = (term223 _25417 _25415 _25416).
Proof. exact (eq_refl (term239 _25415 _25416 _25417)). Qed.
Lemma lem1608488 (_25417 : real) (_25415 : real) (_25416 : real) (h1 : term34) : term223 _25417 _25415 _25416.
Proof. exact (EQ_MP (@lem1608487 _25417 _25415 _25416) (@lem1608486 _25415 _25416 _25417 h1)). Qed.
Lemma lem1608523 (x : real) (y : real) (h1 : term125 x y) : term215 y.
Proof. exact (proj2 (@lem1607956 x y h1)). Qed.
Lemma lem1608543 (_25396 : real) (_25394 : real) (_25395 : real) (h1 : term10) : term240 _25396 _25394 _25395.
Proof. exact (proj2 (@lem1608425 _25396 _25394 _25395 h1)). Qed.
Lemma lem1608571 (x : real) (y : real) (h1 : term129 x y) : term241 x y.
Proof. exact (proj1 (@lem1607957 x y h1)). Qed.
Lemma lem1608603 (_25401 : real) (_25399 : real) (_25400 : real) (h1 : term34) : term242 _25401 _25399 _25400.
Proof. exact (proj1 (@lem1608440 _25401 _25399 _25400 h1)). Qed.
Lemma lem1608623 (y : real) (x : real) (h1 : term211 y x) : term215 x.
Proof. exact (proj2 (@lem1607964 y x h1)). Qed.
Lemma lem1608663 (_25409 : real) (_25407 : real) (_25408 : real) (h1 : term34) : term243 _25409 _25407 _25408.
Proof. exact (proj2 (@lem1608464 _25409 _25407 _25408 h1)). Qed.
Lemma lem1608671 (y : real) (x : real) (h1 : term212 y x) : term241 x y.
Proof. exact (proj1 (@lem1607965 y x h1)). Qed.
Lemma lem1608703 (_25417 : real) (_25415 : real) (_25416 : real) (h1 : term34) : term242 _25417 _25415 _25416.
Proof. exact (proj1 (@lem1608488 _25417 _25415 _25416 h1)). Qed.
Lemma lem1608714 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1608715 (_25421 : real) (_25423 : real) (h1 : _25421 = _25423) : _25421 = _25423.
Proof. exact (h1). Qed.
Lemma lem1608716 (_25422 : real) (_25424 : real) (h1 : _25422 = _25424) : _25422 = _25424.
Proof. exact (h1). Qed.
Lemma lem1608717 (_25421 : real) (_25423 : real) (h1 : _25421 = _25423) : (real_lt _25421) = (real_lt _25423).
Proof. exact (MK_COMB (@lem1608714) (@lem1608715 _25421 _25423 h1)). Qed.
Lemma lem1608718 (_25421 : real) (_25423 : real) (_25422 : real) (_25424 : real) (h1 : _25421 = _25423) (h2 : _25422 = _25424) : (real_lt _25421 _25422) = (real_lt _25423 _25424).
Proof. exact (MK_COMB (@lem1608717 _25421 _25423 h1) (@lem1608716 _25422 _25424 h2)). Qed.
Lemma lem1608720 (b : Prop) (a : Prop) : term244 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1608721 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : term245 _25423 _25424 _25421 _25422.
Proof. exact (@lem1608720 (real_lt _25423 _25424) (real_lt _25421 _25422)). Qed.
Lemma lem1608722 (_25421 : real) (_25423 : real) (_25422 : real) (_25424 : real) (h1 : _25421 = _25423) (h2 : _25422 = _25424) : term246 _25423 _25424 _25421 _25422.
Proof. exact (@lem1608721 _25423 _25424 _25421 _25422 (@lem1608718 _25421 _25423 _25422 _25424 h1 h2)). Qed.
Lemma lem1608723 (_25424 : real) (_25422 : real) (_25421 : real) (_25423 : real) (h1 : _25421 = _25423) : term247 _25423 _25424 _25421 _25422.
Proof. exact (fun h0 : _25422 = _25424 => @lem1608722 _25421 _25423 _25422 _25424 h1 h0). Qed.
Lemma lem1608725 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1608726 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term247 _25423 _25424 _25421 _25422) = (term249 _25423 _25424 _25421 _25422).
Proof. exact (@lem1608725 (_25422 = _25424) (term246 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1608727 (_25424 : real) (_25422 : real) (_25421 : real) (_25423 : real) (h1 : _25421 = _25423) : term249 _25423 _25424 _25421 _25422.
Proof. exact (EQ_MP (@lem1608726 _25423 _25424 _25421 _25422) (@lem1608723 _25424 _25422 _25421 _25423 h1)). Qed.
Lemma lem1608728 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : term250 _25423 _25424 _25421 _25422.
Proof. exact (fun h0 : _25421 = _25423 => @lem1608727 _25424 _25422 _25421 _25423 h0). Qed.
Lemma lem1608730 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1608731 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term250 _25423 _25424 _25421 _25422) = (term251 _25423 _25424 _25421 _25422).
Proof. exact (@lem1608730 (_25421 = _25423) (term249 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1608732 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : term251 _25423 _25424 _25421 _25422.
Proof. exact (EQ_MP (@lem1608731 _25423 _25424 _25421 _25422) (@lem1608728 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1608765 (x : real) (y : real) (z : real) : term252 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1608769 (x : real) (y : real) (h1 : term59 x y) : term56 x.
Proof. exact (proj1 (@lem1607952 x y h1)). Qed.
Lemma lem1608770 (x : real) (y : real) (h1 : term59 x y) : term253 x.
Proof. exact (fun h0 : term215 x => @lem1608769 x y h1). Qed.
Lemma lem1608772 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1608773 (x : real) : (term253 x) = (term56 x).
Proof. exact (@lem1608772 (term56 x)). Qed.
Lemma lem1608774 (x : real) (y : real) (h1 : term59 x y) : term56 x.
Proof. exact (EQ_MP (@lem1608773 x) (@lem1608770 x y h1)). Qed.
Lemma lem1608776 (_25389 : real) (h1 : term41) : (term39 _25389) = term36.
Proof. exact (EQ_MP (@lem1608403 _25389) (@lem1608402 _25389 h1)). Qed.
Lemma lem1608777 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (@lem1608776 x h1). Qed.
Lemma lem1608778 (x : real) (h1 : term41) : term255 x.
Proof. exact (fun h0 : term256 x => @lem1608777 x h1). Qed.
Lemma lem1608780 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1608781 (x : real) : (term255 x) = ((term39 x) = term36).
Proof. exact (@lem1608780 ((term39 x) = term36)). Qed.
Lemma lem1608782 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (EQ_MP (@lem1608781 x) (@lem1608778 x h1)). Qed.
Lemma lem1608784 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1608785 (x : real) : (term39 x) = (term39 x).
Proof. exact (@lem1608784 (term39 x)). Qed.
Lemma lem1608786 (x : real) : term257 x.
Proof. exact (fun h0 : term258 x => @lem1608785 x). Qed.
Lemma lem1608788 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1608789 (x : real) : (term257 x) = ((term39 x) = (term39 x)).
Proof. exact (@lem1608788 ((term39 x) = (term39 x))). Qed.
Lemma lem1608790 (x : real) : (term39 x) = (term39 x).
Proof. exact (EQ_MP (@lem1608789 x) (@lem1608786 x)). Qed.
Lemma lem1608808 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1608809 (y : real) (x : real) (z : real) : (term259 x y z) = (term260 y x z).
Proof. exact (@lem1608808 (y = z) (term261 x z)). Qed.
Lemma lem1608819 (x : real) (y : real) : (term262 x y) = (term262 x y).
Proof. exact (eq_refl (term262 x y)). Qed.
Lemma lem1608820 (y : real) (x : real) (z : real) : (term252 x y z) = (term263 y x z).
Proof. exact (MK_COMB (@lem1608819 x y) (@lem1608809 y x z)). Qed.
Lemma lem1608824 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1608825 (y : real) (x : real) (z : real) : (term263 y x z) = (term265 y x z).
Proof. exact (@lem1608824 (y = z) (term261 x y) (term261 x z)). Qed.
Lemma lem1608847 (y : real) (x : real) (z : real) : (term252 x y z) = (term265 y x z).
Proof. exact (TRANS (@lem1608820 y x z) (@lem1608825 y x z)). Qed.
Lemma lem1608848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1608849 (y : real) (x : real) (z : real) : (term266 x y z) = (term267 y x z).
Proof. exact (MK_COMB (@lem1608848) (@lem1608847 y x z)). Qed.
Lemma lem1608871 (y : real) (x : real) (z : real) : (term265 y x z) = (term265 y x z).
Proof. exact (eq_refl (term265 y x z)). Qed.
Lemma lem1608872 (y : real) (x : real) (z : real) : ((term252 x y z) = (term265 y x z)) = ((term265 y x z) = (term265 y x z)).
Proof. exact (MK_COMB (@lem1608849 y x z) (@lem1608871 y x z)). Qed.
Lemma lem1608874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1608875 (x : Prop) : (x = x) = True.
Proof. exact (@lem1608874 Prop x). Qed.
Lemma lem1608876 (y : real) (x : real) (z : real) : ((term265 y x z) = (term265 y x z)) = True.
Proof. exact (@lem1608875 (term265 y x z)). Qed.
Lemma lem1608877 (y : real) (x : real) (z : real) : ((term252 x y z) = (term265 y x z)) = True.
Proof. exact (TRANS (@lem1608872 y x z) (@lem1608876 y x z)). Qed.
Lemma lem1608878 (y : real) (x : real) (z : real) : True = ((term252 x y z) = (term265 y x z)).
Proof. exact (SYM (@lem1608877 y x z)). Qed.
Lemma lem1608879 (y : real) (x : real) (z : real) : (term252 x y z) = (term265 y x z).
Proof. exact (EQ_MP (@lem1608878 y x z) (@lem0)). Qed.
Lemma lem1608880 (y : real) (x : real) (z : real) : term265 y x z.
Proof. exact (EQ_MP (@lem1608879 y x z) (@lem1608765 x y z)). Qed.
Lemma lem1608882 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1608883 (x : real) (y : real) (z : real) : (term265 y x z) = (term269 x y z).
Proof. exact (@lem1608882 (term270 y x z) (y = z)). Qed.
Lemma lem1608885 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1608886 (y : real) (x : real) (z : real) : (term273 y x z) = (term274 y x z).
Proof. exact (@lem1608885 (term261 x y) (term261 x z)). Qed.
Lemma lem1608888 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1608889 (x : real) (y : real) : (term276 x y) = (x = y).
Proof. exact (@lem1608888 (x = y)). Qed.
Lemma lem1608890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1608891 (x : real) (y : real) : (term277 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1608890) (@lem1608889 x y)). Qed.
Lemma lem1608893 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1608894 (x : real) (z : real) : (term276 x z) = (x = z).
Proof. exact (@lem1608893 (x = z)). Qed.
Lemma lem1608895 (y : real) (x : real) (z : real) : (term274 y x z) = (term279 y x z).
Proof. exact (MK_COMB (@lem1608891 x y) (@lem1608894 x z)). Qed.
Lemma lem1608896 (y : real) (x : real) (z : real) : (term273 y x z) = (term279 y x z).
Proof. exact (TRANS (@lem1608886 y x z) (@lem1608895 y x z)). Qed.
Lemma lem1608897 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1608898 (y : real) (x : real) (z : real) : (term280 y x z) = (term281 y x z).
Proof. exact (MK_COMB (@lem1608897) (@lem1608896 y x z)). Qed.
Lemma lem1608899 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1608900 (x : real) (y : real) (z : real) : (term269 x y z) = (term282 x y z).
Proof. exact (MK_COMB (@lem1608898 y x z) (@lem1608899 y z)). Qed.
Lemma lem1608901 (x : real) (y : real) (z : real) : (term265 y x z) = (term282 x y z).
Proof. exact (TRANS (@lem1608883 x y z) (@lem1608900 x y z)). Qed.
Lemma lem1608903 (x : real) (h1 : term41) : term283 x.
Proof. exact (conj (@lem1608782 x h1) (@lem1608790 x)). Qed.
Lemma lem1608905 (x : real) (y : real) (z : real) : term282 x y z.
Proof. exact (EQ_MP (@lem1608901 x y z) (@lem1608880 y x z)). Qed.
Lemma lem1608906 (x : real) : term284 x.
Proof. exact (@lem1608905 (term39 x) term36 (term39 x)). Qed.
Lemma lem1608909 (x : real) (h1 : term41) : term36 = (term39 x).
Proof. exact (@lem1608906 x (@lem1608903 x h1)). Qed.
Lemma lem1608910 (x : real) (h1 : term41) : term285 x.
Proof. exact (fun h0 : term286 x => @lem1608909 x h1). Qed.
Lemma lem1608912 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1608913 (x : real) : (term285 x) = (term36 = (term39 x)).
Proof. exact (@lem1608912 (term36 = (term39 x))). Qed.
Lemma lem1608914 (x : real) (h1 : term41) : term36 = (term39 x).
Proof. exact (EQ_MP (@lem1608913 x) (@lem1608910 x h1)). Qed.
Lemma lem1608916 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1608917 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1608916 (real_mul x y)). Qed.
Lemma lem1608918 (x : real) (y : real) : term287 x y.
Proof. exact (fun h0 : term288 x y => @lem1608917 x y). Qed.
Lemma lem1608920 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1608921 (x : real) (y : real) : (term287 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1608920 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1608922 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1608921 x y) (@lem1608918 x y)). Qed.
Lemma lem1608924 (x : real) (y : real) (h1 : term125 x y) : term55 x y.
Proof. exact (proj1 (@lem1607956 x y h1)). Qed.
Lemma lem1608925 (x : real) (y : real) (h1 : term125 x y) : term289 x y.
Proof. exact (fun h0 : term241 x y => @lem1608924 x y h1). Qed.
Lemma lem1608927 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1608928 (x : real) (y : real) : (term289 x y) = (term55 x y).
Proof. exact (@lem1608927 (term55 x y)). Qed.
Lemma lem1608929 (x : real) (y : real) (h1 : term125 x y) : term55 x y.
Proof. exact (EQ_MP (@lem1608928 x y) (@lem1608925 x y h1)). Qed.
Lemma lem1608947 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1608948 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term249 _25423 _25424 _25421 _25422) = (term290 _25423 _25424 _25421 _25422).
Proof. exact (@lem1608947 (real_lt _25423 _25424) (term261 _25422 _25424) (term291 _25421 _25422)). Qed.
Lemma lem1608966 (_25421 : real) (_25423 : real) : (term262 _25421 _25423) = (term262 _25421 _25423).
Proof. exact (eq_refl (term262 _25421 _25423)). Qed.
Lemma lem1608967 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term251 _25423 _25424 _25421 _25422) = (term292 _25423 _25424 _25421 _25422).
Proof. exact (MK_COMB (@lem1608966 _25421 _25423) (@lem1608948 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1608971 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1608972 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term292 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422).
Proof. exact (@lem1608971 (real_lt _25423 _25424) (term261 _25421 _25423) (term294 _25424 _25421 _25422)). Qed.
Lemma lem1609002 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term251 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422).
Proof. exact (TRANS (@lem1608967 _25423 _25424 _25421 _25422) (@lem1608972 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1609004 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term295 _25423 _25424 _25421 _25422) = (term296 _25423 _25424 _25421 _25422).
Proof. exact (MK_COMB (@lem1609003) (@lem1609002 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609034 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term293 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422).
Proof. exact (eq_refl (term293 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609035 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : ((term251 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422)) = ((term293 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422)).
Proof. exact (MK_COMB (@lem1609004 _25423 _25424 _25421 _25422) (@lem1609034 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609037 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1609038 (x : Prop) : (x = x) = True.
Proof. exact (@lem1609037 Prop x). Qed.
Lemma lem1609039 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : ((term293 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422)) = True.
Proof. exact (@lem1609038 (term293 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609040 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : ((term251 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422)) = True.
Proof. exact (TRANS (@lem1609035 _25423 _25424 _25421 _25422) (@lem1609039 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609041 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : True = ((term251 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422)).
Proof. exact (SYM (@lem1609040 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609042 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term251 _25423 _25424 _25421 _25422) = (term293 _25423 _25424 _25421 _25422).
Proof. exact (EQ_MP (@lem1609041 _25423 _25424 _25421 _25422) (@lem0)). Qed.
Lemma lem1609043 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : term293 _25423 _25424 _25421 _25422.
Proof. exact (EQ_MP (@lem1609042 _25423 _25424 _25421 _25422) (@lem1608732 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609045 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1609046 (_25421 : real) (_25422 : real) (_25423 : real) (_25424 : real) : (term293 _25423 _25424 _25421 _25422) = (term297 _25421 _25422 _25423 _25424).
Proof. exact (@lem1609045 (term298 _25423 _25424 _25421 _25422) (real_lt _25423 _25424)). Qed.
Lemma lem1609048 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609049 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term299 _25423 _25424 _25421 _25422) = (term300 _25423 _25424 _25421 _25422).
Proof. exact (@lem1609048 (term261 _25421 _25423) (term294 _25424 _25421 _25422)). Qed.
Lemma lem1609051 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609052 (_25421 : real) (_25423 : real) : (term276 _25421 _25423) = (_25421 = _25423).
Proof. exact (@lem1609051 (_25421 = _25423)). Qed.
Lemma lem1609053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609054 (_25421 : real) (_25423 : real) : (term277 _25421 _25423) = (term278 _25421 _25423).
Proof. exact (MK_COMB (@lem1609053) (@lem1609052 _25421 _25423)). Qed.
Lemma lem1609056 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609057 (_25424 : real) (_25421 : real) (_25422 : real) : (term301 _25424 _25421 _25422) = (term302 _25424 _25421 _25422).
Proof. exact (@lem1609056 (term261 _25422 _25424) (term291 _25421 _25422)). Qed.
Lemma lem1609059 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609060 (_25422 : real) (_25424 : real) : (term276 _25422 _25424) = (_25422 = _25424).
Proof. exact (@lem1609059 (_25422 = _25424)). Qed.
Lemma lem1609061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609062 (_25422 : real) (_25424 : real) : (term277 _25422 _25424) = (term278 _25422 _25424).
Proof. exact (MK_COMB (@lem1609061) (@lem1609060 _25422 _25424)). Qed.
Lemma lem1609064 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609065 (_25421 : real) (_25422 : real) : (term303 _25421 _25422) = (real_lt _25421 _25422).
Proof. exact (@lem1609064 (real_lt _25421 _25422)). Qed.
Lemma lem1609066 (_25424 : real) (_25421 : real) (_25422 : real) : (term302 _25424 _25421 _25422) = (term304 _25424 _25421 _25422).
Proof. exact (MK_COMB (@lem1609062 _25422 _25424) (@lem1609065 _25421 _25422)). Qed.
Lemma lem1609067 (_25424 : real) (_25421 : real) (_25422 : real) : (term301 _25424 _25421 _25422) = (term304 _25424 _25421 _25422).
Proof. exact (TRANS (@lem1609057 _25424 _25421 _25422) (@lem1609066 _25424 _25421 _25422)). Qed.
Lemma lem1609068 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term300 _25423 _25424 _25421 _25422) = (term305 _25423 _25424 _25421 _25422).
Proof. exact (MK_COMB (@lem1609054 _25421 _25423) (@lem1609067 _25424 _25421 _25422)). Qed.
Lemma lem1609069 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term299 _25423 _25424 _25421 _25422) = (term305 _25423 _25424 _25421 _25422).
Proof. exact (TRANS (@lem1609049 _25423 _25424 _25421 _25422) (@lem1609068 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1609071 (_25423 : real) (_25424 : real) (_25421 : real) (_25422 : real) : (term306 _25423 _25424 _25421 _25422) = (term307 _25423 _25424 _25421 _25422).
Proof. exact (MK_COMB (@lem1609070) (@lem1609069 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609072 (_25423 : real) (_25424 : real) : (real_lt _25423 _25424) = (real_lt _25423 _25424).
Proof. exact (eq_refl (real_lt _25423 _25424)). Qed.
Lemma lem1609073 (_25421 : real) (_25422 : real) (_25423 : real) (_25424 : real) : (term297 _25421 _25422 _25423 _25424) = (term308 _25421 _25422 _25423 _25424).
Proof. exact (MK_COMB (@lem1609071 _25423 _25424 _25421 _25422) (@lem1609072 _25423 _25424)). Qed.
Lemma lem1609074 (_25421 : real) (_25422 : real) (_25423 : real) (_25424 : real) : (term293 _25423 _25424 _25421 _25422) = (term308 _25421 _25422 _25423 _25424).
Proof. exact (TRANS (@lem1609046 _25421 _25422 _25423 _25424) (@lem1609073 _25421 _25422 _25423 _25424)). Qed.
Lemma lem1609076 (x : real) (y : real) (h1 : term125 x y) : term309 x y.
Proof. exact (conj (@lem1608922 x y) (@lem1608929 x y h1)). Qed.
Lemma lem1609077 (x : real) (y : real) (h1 : term41) (h2 : term125 x y) : term310 x y.
Proof. exact (conj (@lem1608914 x h1) (@lem1609076 x y h2)). Qed.
Lemma lem1609079 (_25421 : real) (_25422 : real) (_25423 : real) (_25424 : real) : term308 _25421 _25422 _25423 _25424.
Proof. exact (EQ_MP (@lem1609074 _25421 _25422 _25423 _25424) (@lem1609043 _25423 _25424 _25421 _25422)). Qed.
Lemma lem1609080 (x : real) (y : real) : term311 x y.
Proof. exact (@lem1609079 term36 (real_mul x y) (term39 x) (real_mul x y)). Qed.
Lemma lem1609083 (x : real) (y : real) (h1 : term41) (h2 : term125 x y) : term312 x y.
Proof. exact (@lem1609080 x y (@lem1609077 x y h1 h2)). Qed.
Lemma lem1609084 (x : real) (y : real) (h1 : term41) (h2 : term125 x y) : term313 x y.
Proof. exact (fun h0 : term314 x y => @lem1609083 x y h1 h2). Qed.
Lemma lem1609086 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609087 (x : real) (y : real) : (term313 x y) = (term312 x y).
Proof. exact (@lem1609086 (term312 x y)). Qed.
Lemma lem1609088 (x : real) (y : real) (h1 : term41) (h2 : term125 x y) : term312 x y.
Proof. exact (EQ_MP (@lem1609087 x y) (@lem1609084 x y h1 h2)). Qed.
Lemma lem1609094 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609095 (_25396 : real) (_25394 : real) (_25395 : real) : (term240 _25396 _25394 _25395) = (term315 _25396 _25394 _25395).
Proof. exact (@lem1609094 (term316 _25394 _25396 _25395) (term215 _25396) (real_lt _25394 _25395)). Qed.
Lemma lem1609109 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1609110 (_25394 : real) (_25395 : real) (_25396 : real) : (term317 _25396 _25394 _25395) = (term318 _25394 _25395 _25396).
Proof. exact (@lem1609109 (real_lt _25394 _25395) (term215 _25396)). Qed.
Lemma lem1609116 (_25394 : real) (_25396 : real) (_25395 : real) : (term319 _25394 _25396 _25395) = (term319 _25394 _25396 _25395).
Proof. exact (eq_refl (term319 _25394 _25396 _25395)). Qed.
Lemma lem1609117 (_25394 : real) (_25395 : real) (_25396 : real) : (term315 _25396 _25394 _25395) = (term320 _25394 _25395 _25396).
Proof. exact (MK_COMB (@lem1609116 _25394 _25396 _25395) (@lem1609110 _25394 _25395 _25396)). Qed.
Lemma lem1609121 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609122 (_25394 : real) (_25395 : real) (_25396 : real) : (term320 _25394 _25395 _25396) = (term321 _25394 _25395 _25396).
Proof. exact (@lem1609121 (real_lt _25394 _25395) (term316 _25394 _25396 _25395) (term215 _25396)). Qed.
Lemma lem1609138 (_25394 : real) (_25395 : real) (_25396 : real) : (term315 _25396 _25394 _25395) = (term321 _25394 _25395 _25396).
Proof. exact (TRANS (@lem1609117 _25394 _25395 _25396) (@lem1609122 _25394 _25395 _25396)). Qed.
Lemma lem1609139 (_25394 : real) (_25395 : real) (_25396 : real) : (term240 _25396 _25394 _25395) = (term321 _25394 _25395 _25396).
Proof. exact (TRANS (@lem1609095 _25396 _25394 _25395) (@lem1609138 _25394 _25395 _25396)). Qed.
Lemma lem1609140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1609141 (_25394 : real) (_25395 : real) (_25396 : real) : (term322 _25396 _25394 _25395) = (term323 _25394 _25395 _25396).
Proof. exact (MK_COMB (@lem1609140) (@lem1609139 _25394 _25395 _25396)). Qed.
Lemma lem1609155 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1609156 (_25394 : real) (_25395 : real) (_25396 : real) : (term324 _25394 _25396 _25395) = (term325 _25394 _25395 _25396).
Proof. exact (@lem1609155 (term316 _25394 _25396 _25395) (term215 _25396)). Qed.
Lemma lem1609162 (_25394 : real) (_25395 : real) : (term326 _25394 _25395) = (term326 _25394 _25395).
Proof. exact (eq_refl (term326 _25394 _25395)). Qed.
Lemma lem1609163 (_25394 : real) (_25395 : real) (_25396 : real) : (term327 _25394 _25396 _25395) = (term321 _25394 _25395 _25396).
Proof. exact (MK_COMB (@lem1609162 _25394 _25395) (@lem1609156 _25394 _25395 _25396)). Qed.
Lemma lem1609174 (_25394 : real) (_25395 : real) (_25396 : real) : ((term240 _25396 _25394 _25395) = (term327 _25394 _25396 _25395)) = ((term321 _25394 _25395 _25396) = (term321 _25394 _25395 _25396)).
Proof. exact (MK_COMB (@lem1609141 _25394 _25395 _25396) (@lem1609163 _25394 _25395 _25396)). Qed.
Lemma lem1609176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1609177 (x : Prop) : (x = x) = True.
Proof. exact (@lem1609176 Prop x). Qed.
Lemma lem1609178 (_25394 : real) (_25395 : real) (_25396 : real) : ((term321 _25394 _25395 _25396) = (term321 _25394 _25395 _25396)) = True.
Proof. exact (@lem1609177 (term321 _25394 _25395 _25396)). Qed.
Lemma lem1609179 (_25394 : real) (_25396 : real) (_25395 : real) : ((term240 _25396 _25394 _25395) = (term327 _25394 _25396 _25395)) = True.
Proof. exact (TRANS (@lem1609174 _25394 _25395 _25396) (@lem1609178 _25394 _25395 _25396)). Qed.
Lemma lem1609180 (_25394 : real) (_25396 : real) (_25395 : real) : True = ((term240 _25396 _25394 _25395) = (term327 _25394 _25396 _25395)).
Proof. exact (SYM (@lem1609179 _25394 _25396 _25395)). Qed.
Lemma lem1609181 (_25394 : real) (_25396 : real) (_25395 : real) : (term240 _25396 _25394 _25395) = (term327 _25394 _25396 _25395).
Proof. exact (EQ_MP (@lem1609180 _25394 _25396 _25395) (@lem0)). Qed.
Lemma lem1609182 (_25394 : real) (_25396 : real) (_25395 : real) (h1 : term10) : term327 _25394 _25396 _25395.
Proof. exact (EQ_MP (@lem1609181 _25394 _25396 _25395) (@lem1608543 _25396 _25394 _25395 h1)). Qed.
Lemma lem1609184 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1609185 (_25396 : real) (_25394 : real) (_25395 : real) : (term327 _25394 _25396 _25395) = (term328 _25396 _25394 _25395).
Proof. exact (@lem1609184 (term324 _25394 _25396 _25395) (real_lt _25394 _25395)). Qed.
Lemma lem1609187 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609188 (_25394 : real) (_25396 : real) (_25395 : real) : (term329 _25394 _25396 _25395) = (term330 _25394 _25396 _25395).
Proof. exact (@lem1609187 (term215 _25396) (term316 _25394 _25396 _25395)). Qed.
Lemma lem1609190 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609191 (_25396 : real) : (term331 _25396) = (term56 _25396).
Proof. exact (@lem1609190 (term56 _25396)). Qed.
Lemma lem1609192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609193 (_25396 : real) : (term332 _25396) = (term57 _25396).
Proof. exact (MK_COMB (@lem1609192) (@lem1609191 _25396)). Qed.
Lemma lem1609195 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609196 (_25394 : real) (_25396 : real) (_25395 : real) : (term333 _25394 _25396 _25395) = (term201 _25394 _25396 _25395).
Proof. exact (@lem1609195 (term201 _25394 _25396 _25395)). Qed.
Lemma lem1609197 (_25394 : real) (_25396 : real) (_25395 : real) : (term330 _25394 _25396 _25395) = (term334 _25394 _25396 _25395).
Proof. exact (MK_COMB (@lem1609193 _25396) (@lem1609196 _25394 _25396 _25395)). Qed.
Lemma lem1609198 (_25394 : real) (_25396 : real) (_25395 : real) : (term329 _25394 _25396 _25395) = (term334 _25394 _25396 _25395).
Proof. exact (TRANS (@lem1609188 _25394 _25396 _25395) (@lem1609197 _25394 _25396 _25395)). Qed.
Lemma lem1609199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1609200 (_25394 : real) (_25396 : real) (_25395 : real) : (term335 _25394 _25396 _25395) = (term336 _25394 _25396 _25395).
Proof. exact (MK_COMB (@lem1609199) (@lem1609198 _25394 _25396 _25395)). Qed.
Lemma lem1609201 (_25394 : real) (_25395 : real) : (real_lt _25394 _25395) = (real_lt _25394 _25395).
Proof. exact (eq_refl (real_lt _25394 _25395)). Qed.
Lemma lem1609202 (_25396 : real) (_25394 : real) (_25395 : real) : (term328 _25396 _25394 _25395) = (term337 _25396 _25394 _25395).
Proof. exact (MK_COMB (@lem1609200 _25394 _25396 _25395) (@lem1609201 _25394 _25395)). Qed.
Lemma lem1609203 (_25396 : real) (_25394 : real) (_25395 : real) : (term327 _25394 _25396 _25395) = (term337 _25396 _25394 _25395).
Proof. exact (TRANS (@lem1609185 _25396 _25394 _25395) (@lem1609202 _25396 _25394 _25395)). Qed.
Lemma lem1609205 (x : real) (y : real) (h1 : term41) (h2 : term59 x y) (h3 : term125 x y) : term338 x y.
Proof. exact (conj (@lem1608774 x y h2) (@lem1609088 x y h1 h3)). Qed.
Lemma lem1609207 (_25396 : real) (_25394 : real) (_25395 : real) (h1 : term10) : term337 _25396 _25394 _25395.
Proof. exact (EQ_MP (@lem1609203 _25396 _25394 _25395) (@lem1609182 _25394 _25396 _25395 h1)). Qed.
Lemma lem1609208 (x : real) (y : real) (h1 : term10) : term339 x y.
Proof. exact (@lem1609207 x term36 y h1). Qed.
Lemma lem1609211 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : term56 y.
Proof. exact (@lem1609208 x y h1 (@lem1609205 x y h2 h3 h4)). Qed.
Lemma lem1609212 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : term253 y.
Proof. exact (fun h0 : term215 y => @lem1609211 x y h1 h2 h3 h4). Qed.
Lemma lem1609214 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609215 (y : real) : (term253 y) = (term56 y).
Proof. exact (@lem1609214 (term56 y)). Qed.
Lemma lem1609216 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : term56 y.
Proof. exact (EQ_MP (@lem1609215 y) (@lem1609212 x y h1 h2 h3 h4)). Qed.
Lemma lem1609219 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1609221 (y : real) : (term215 y) = (term340 y).
Proof. exact (@lem1609219 (term56 y)). Qed.
Lemma lem1609224 (x : real) (y : real) (h1 : term125 x y) : term340 y.
Proof. exact (EQ_MP (@lem1609221 y) (@lem1608523 x y h1)). Qed.
Lemma lem1609227 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : False.
Proof. exact (@lem1609224 x y h4 (@lem1609216 x y h1 h2 h3 h4)). Qed.
Lemma lem1609228 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : term341.
Proof. exact (fun h0 : ~ False => @lem1609227 x y h1 h2 h3 h4). Qed.
Lemma lem1609230 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609231 : term341 = False.
Proof. exact (@lem1609230 False). Qed.
Lemma lem1609232 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : False.
Proof. exact (EQ_MP (@lem1609231) (@lem1609228 x y h1 h2 h3 h4)). Qed.
Lemma lem1609233 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1609234 (_25433 : real) (_25435 : real) (h1 : _25433 = _25435) : _25433 = _25435.
Proof. exact (h1). Qed.
Lemma lem1609235 (_25434 : real) (_25436 : real) (h1 : _25434 = _25436) : _25434 = _25436.
Proof. exact (h1). Qed.
Lemma lem1609236 (_25433 : real) (_25435 : real) (h1 : _25433 = _25435) : (real_lt _25433) = (real_lt _25435).
Proof. exact (MK_COMB (@lem1609233) (@lem1609234 _25433 _25435 h1)). Qed.
Lemma lem1609237 (_25433 : real) (_25435 : real) (_25434 : real) (_25436 : real) (h1 : _25433 = _25435) (h2 : _25434 = _25436) : (real_lt _25433 _25434) = (real_lt _25435 _25436).
Proof. exact (MK_COMB (@lem1609236 _25433 _25435 h1) (@lem1609235 _25434 _25436 h2)). Qed.
Lemma lem1609239 (b : Prop) (a : Prop) : term244 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1609240 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : term245 _25435 _25436 _25433 _25434.
Proof. exact (@lem1609239 (real_lt _25435 _25436) (real_lt _25433 _25434)). Qed.
Lemma lem1609241 (_25433 : real) (_25435 : real) (_25434 : real) (_25436 : real) (h1 : _25433 = _25435) (h2 : _25434 = _25436) : term246 _25435 _25436 _25433 _25434.
Proof. exact (@lem1609240 _25435 _25436 _25433 _25434 (@lem1609237 _25433 _25435 _25434 _25436 h1 h2)). Qed.
Lemma lem1609242 (_25436 : real) (_25434 : real) (_25433 : real) (_25435 : real) (h1 : _25433 = _25435) : term247 _25435 _25436 _25433 _25434.
Proof. exact (fun h0 : _25434 = _25436 => @lem1609241 _25433 _25435 _25434 _25436 h1 h0). Qed.
Lemma lem1609244 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1609245 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term247 _25435 _25436 _25433 _25434) = (term249 _25435 _25436 _25433 _25434).
Proof. exact (@lem1609244 (_25434 = _25436) (term246 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609246 (_25436 : real) (_25434 : real) (_25433 : real) (_25435 : real) (h1 : _25433 = _25435) : term249 _25435 _25436 _25433 _25434.
Proof. exact (EQ_MP (@lem1609245 _25435 _25436 _25433 _25434) (@lem1609242 _25436 _25434 _25433 _25435 h1)). Qed.
Lemma lem1609247 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : term250 _25435 _25436 _25433 _25434.
Proof. exact (fun h0 : _25433 = _25435 => @lem1609246 _25436 _25434 _25433 _25435 h0). Qed.
Lemma lem1609249 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1609250 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term250 _25435 _25436 _25433 _25434) = (term251 _25435 _25436 _25433 _25434).
Proof. exact (@lem1609249 (_25433 = _25435) (term249 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609251 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : term251 _25435 _25436 _25433 _25434.
Proof. exact (EQ_MP (@lem1609250 _25435 _25436 _25433 _25434) (@lem1609247 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609288 (_25398 : real) (h1 : term38) : (term35 _25398) = term36.
Proof. exact (EQ_MP (@lem1608430 _25398) (@lem1608429 _25398 h1)). Qed.
Lemma lem1609289 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (@lem1609288 y h1). Qed.
Lemma lem1609290 (y : real) (h1 : term38) : term342 y.
Proof. exact (fun h0 : term343 y => @lem1609289 y h1). Qed.
Lemma lem1609292 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609293 (y : real) : (term342 y) = ((term35 y) = term36).
Proof. exact (@lem1609292 ((term35 y) = term36)). Qed.
Lemma lem1609294 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (EQ_MP (@lem1609293 y) (@lem1609290 y h1)). Qed.
Lemma lem1609296 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1609297 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1609296 (real_mul x y)). Qed.
Lemma lem1609298 (x : real) (y : real) : term287 x y.
Proof. exact (fun h0 : term288 x y => @lem1609297 x y). Qed.
Lemma lem1609300 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609301 (x : real) (y : real) : (term287 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1609300 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1609302 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1609301 x y) (@lem1609298 x y)). Qed.
Lemma lem1609304 (x : real) (y : real) (h1 : term129 x y) : term56 y.
Proof. exact (proj2 (@lem1607957 x y h1)). Qed.
Lemma lem1609305 (x : real) (y : real) (h1 : term129 x y) : term253 y.
Proof. exact (fun h0 : term215 y => @lem1609304 x y h1). Qed.
Lemma lem1609307 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609308 (y : real) : (term253 y) = (term56 y).
Proof. exact (@lem1609307 (term56 y)). Qed.
Lemma lem1609309 (x : real) (y : real) (h1 : term129 x y) : term56 y.
Proof. exact (EQ_MP (@lem1609308 y) (@lem1609305 x y h1)). Qed.
Lemma lem1609311 (x : real) (y : real) (h1 : term59 x y) : term56 x.
Proof. exact (proj1 (@lem1607952 x y h1)). Qed.
Lemma lem1609312 (x : real) (y : real) (h1 : term59 x y) : term253 x.
Proof. exact (fun h0 : term215 x => @lem1609311 x y h1). Qed.
Lemma lem1609314 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609315 (x : real) : (term253 x) = (term56 x).
Proof. exact (@lem1609314 (term56 x)). Qed.
Lemma lem1609316 (x : real) (y : real) (h1 : term59 x y) : term56 x.
Proof. exact (EQ_MP (@lem1609315 x) (@lem1609312 x y h1)). Qed.
Lemma lem1609322 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609323 (_25401 : real) (_25399 : real) (_25400 : real) : (term242 _25401 _25399 _25400) = (term344 _25401 _25399 _25400).
Proof. exact (@lem1609322 (term190 _25399 _25400 _25401) (term215 _25401) (term291 _25399 _25400)). Qed.
Lemma lem1609337 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1609338 (_25399 : real) (_25400 : real) (_25401 : real) : (term345 _25401 _25399 _25400) = (term346 _25399 _25400 _25401).
Proof. exact (@lem1609337 (term291 _25399 _25400) (term215 _25401)). Qed.
Lemma lem1609344 (_25399 : real) (_25400 : real) (_25401 : real) : (term347 _25399 _25400 _25401) = (term347 _25399 _25400 _25401).
Proof. exact (eq_refl (term347 _25399 _25400 _25401)). Qed.
Lemma lem1609345 (_25399 : real) (_25400 : real) (_25401 : real) : (term344 _25401 _25399 _25400) = (term348 _25399 _25400 _25401).
Proof. exact (MK_COMB (@lem1609344 _25399 _25400 _25401) (@lem1609338 _25399 _25400 _25401)). Qed.
Lemma lem1609356 (_25399 : real) (_25400 : real) (_25401 : real) : (term242 _25401 _25399 _25400) = (term348 _25399 _25400 _25401).
Proof. exact (TRANS (@lem1609323 _25401 _25399 _25400) (@lem1609345 _25399 _25400 _25401)). Qed.
Lemma lem1609357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1609358 (_25399 : real) (_25400 : real) (_25401 : real) : (term349 _25401 _25399 _25400) = (term350 _25399 _25400 _25401).
Proof. exact (MK_COMB (@lem1609357) (@lem1609356 _25399 _25400 _25401)). Qed.
Lemma lem1609372 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1609373 (_25399 : real) (_25400 : real) (_25401 : real) : (term345 _25401 _25399 _25400) = (term346 _25399 _25400 _25401).
Proof. exact (@lem1609372 (term291 _25399 _25400) (term215 _25401)). Qed.
Lemma lem1609379 (_25399 : real) (_25400 : real) (_25401 : real) : (term347 _25399 _25400 _25401) = (term347 _25399 _25400 _25401).
Proof. exact (eq_refl (term347 _25399 _25400 _25401)). Qed.
Lemma lem1609380 (_25399 : real) (_25400 : real) (_25401 : real) : (term344 _25401 _25399 _25400) = (term348 _25399 _25400 _25401).
Proof. exact (MK_COMB (@lem1609379 _25399 _25400 _25401) (@lem1609373 _25399 _25400 _25401)). Qed.
Lemma lem1609391 (_25399 : real) (_25400 : real) (_25401 : real) : ((term242 _25401 _25399 _25400) = (term344 _25401 _25399 _25400)) = ((term348 _25399 _25400 _25401) = (term348 _25399 _25400 _25401)).
Proof. exact (MK_COMB (@lem1609358 _25399 _25400 _25401) (@lem1609380 _25399 _25400 _25401)). Qed.
Lemma lem1609393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1609394 (x : Prop) : (x = x) = True.
Proof. exact (@lem1609393 Prop x). Qed.
Lemma lem1609395 (_25399 : real) (_25400 : real) (_25401 : real) : ((term348 _25399 _25400 _25401) = (term348 _25399 _25400 _25401)) = True.
Proof. exact (@lem1609394 (term348 _25399 _25400 _25401)). Qed.
Lemma lem1609396 (_25401 : real) (_25399 : real) (_25400 : real) : ((term242 _25401 _25399 _25400) = (term344 _25401 _25399 _25400)) = True.
Proof. exact (TRANS (@lem1609391 _25399 _25400 _25401) (@lem1609395 _25399 _25400 _25401)). Qed.
Lemma lem1609397 (_25401 : real) (_25399 : real) (_25400 : real) : True = ((term242 _25401 _25399 _25400) = (term344 _25401 _25399 _25400)).
Proof. exact (SYM (@lem1609396 _25401 _25399 _25400)). Qed.
Lemma lem1609398 (_25401 : real) (_25399 : real) (_25400 : real) : (term242 _25401 _25399 _25400) = (term344 _25401 _25399 _25400).
Proof. exact (EQ_MP (@lem1609397 _25401 _25399 _25400) (@lem0)). Qed.
Lemma lem1609399 (_25401 : real) (_25399 : real) (_25400 : real) (h1 : term34) : term344 _25401 _25399 _25400.
Proof. exact (EQ_MP (@lem1609398 _25401 _25399 _25400) (@lem1608603 _25401 _25399 _25400 h1)). Qed.
Lemma lem1609401 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1609402 (_25399 : real) (_25400 : real) (_25401 : real) : (term344 _25401 _25399 _25400) = (term351 _25399 _25400 _25401).
Proof. exact (@lem1609401 (term345 _25401 _25399 _25400) (term190 _25399 _25400 _25401)). Qed.
Lemma lem1609404 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609405 (_25401 : real) (_25399 : real) (_25400 : real) : (term352 _25401 _25399 _25400) = (term353 _25401 _25399 _25400).
Proof. exact (@lem1609404 (term215 _25401) (term291 _25399 _25400)). Qed.
Lemma lem1609407 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609408 (_25401 : real) : (term331 _25401) = (term56 _25401).
Proof. exact (@lem1609407 (term56 _25401)). Qed.
Lemma lem1609409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609410 (_25401 : real) : (term332 _25401) = (term57 _25401).
Proof. exact (MK_COMB (@lem1609409) (@lem1609408 _25401)). Qed.
Lemma lem1609412 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609413 (_25399 : real) (_25400 : real) : (term303 _25399 _25400) = (real_lt _25399 _25400).
Proof. exact (@lem1609412 (real_lt _25399 _25400)). Qed.
Lemma lem1609414 (_25401 : real) (_25399 : real) (_25400 : real) : (term353 _25401 _25399 _25400) = (term354 _25401 _25399 _25400).
Proof. exact (MK_COMB (@lem1609410 _25401) (@lem1609413 _25399 _25400)). Qed.
Lemma lem1609415 (_25401 : real) (_25399 : real) (_25400 : real) : (term352 _25401 _25399 _25400) = (term354 _25401 _25399 _25400).
Proof. exact (TRANS (@lem1609405 _25401 _25399 _25400) (@lem1609414 _25401 _25399 _25400)). Qed.
Lemma lem1609416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1609417 (_25401 : real) (_25399 : real) (_25400 : real) : (term355 _25401 _25399 _25400) = (term356 _25401 _25399 _25400).
Proof. exact (MK_COMB (@lem1609416) (@lem1609415 _25401 _25399 _25400)). Qed.
Lemma lem1609418 (_25399 : real) (_25400 : real) (_25401 : real) : (term190 _25399 _25400 _25401) = (term190 _25399 _25400 _25401).
Proof. exact (eq_refl (term190 _25399 _25400 _25401)). Qed.
Lemma lem1609419 (_25399 : real) (_25400 : real) (_25401 : real) : (term351 _25399 _25400 _25401) = (term357 _25399 _25400 _25401).
Proof. exact (MK_COMB (@lem1609417 _25401 _25399 _25400) (@lem1609418 _25399 _25400 _25401)). Qed.
Lemma lem1609420 (_25399 : real) (_25400 : real) (_25401 : real) : (term344 _25401 _25399 _25400) = (term357 _25399 _25400 _25401).
Proof. exact (TRANS (@lem1609402 _25399 _25400 _25401) (@lem1609419 _25399 _25400 _25401)). Qed.
Lemma lem1609422 (x : real) (y : real) (h1 : term129 x y) (h2 : term59 x y) : term358 y x.
Proof. exact (conj (@lem1609309 x y h1) (@lem1609316 x y h2)). Qed.
Lemma lem1609424 (_25399 : real) (_25400 : real) (_25401 : real) (h1 : term34) : term357 _25399 _25400 _25401.
Proof. exact (EQ_MP (@lem1609420 _25399 _25400 _25401) (@lem1609399 _25401 _25399 _25400 h1)). Qed.
Lemma lem1609425 (x : real) (y : real) (h1 : term34) : term359 x y.
Proof. exact (@lem1609424 term36 x y h1). Qed.
Lemma lem1609428 (x : real) (y : real) (h1 : term34) (h2 : term129 x y) (h3 : term59 x y) : term360 x y.
Proof. exact (@lem1609425 x y h1 (@lem1609422 x y h2 h3)). Qed.
Lemma lem1609429 (x : real) (y : real) (h1 : term34) (h2 : term129 x y) (h3 : term59 x y) : term361 x y.
Proof. exact (fun h0 : term362 x y => @lem1609428 x y h1 h2 h3). Qed.
Lemma lem1609431 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609432 (x : real) (y : real) : (term361 x y) = (term360 x y).
Proof. exact (@lem1609431 (term360 x y)). Qed.
Lemma lem1609433 (x : real) (y : real) (h1 : term34) (h2 : term129 x y) (h3 : term59 x y) : term360 x y.
Proof. exact (EQ_MP (@lem1609432 x y) (@lem1609429 x y h1 h2 h3)). Qed.
Lemma lem1609451 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609452 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term249 _25435 _25436 _25433 _25434) = (term290 _25435 _25436 _25433 _25434).
Proof. exact (@lem1609451 (real_lt _25435 _25436) (term261 _25434 _25436) (term291 _25433 _25434)). Qed.
Lemma lem1609470 (_25433 : real) (_25435 : real) : (term262 _25433 _25435) = (term262 _25433 _25435).
Proof. exact (eq_refl (term262 _25433 _25435)). Qed.
Lemma lem1609471 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term251 _25435 _25436 _25433 _25434) = (term292 _25435 _25436 _25433 _25434).
Proof. exact (MK_COMB (@lem1609470 _25433 _25435) (@lem1609452 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609475 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609476 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term292 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434).
Proof. exact (@lem1609475 (real_lt _25435 _25436) (term261 _25433 _25435) (term294 _25436 _25433 _25434)). Qed.
Lemma lem1609506 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term251 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434).
Proof. exact (TRANS (@lem1609471 _25435 _25436 _25433 _25434) (@lem1609476 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1609508 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term295 _25435 _25436 _25433 _25434) = (term296 _25435 _25436 _25433 _25434).
Proof. exact (MK_COMB (@lem1609507) (@lem1609506 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609538 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term293 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434).
Proof. exact (eq_refl (term293 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609539 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : ((term251 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434)) = ((term293 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434)).
Proof. exact (MK_COMB (@lem1609508 _25435 _25436 _25433 _25434) (@lem1609538 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609541 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1609542 (x : Prop) : (x = x) = True.
Proof. exact (@lem1609541 Prop x). Qed.
Lemma lem1609543 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : ((term293 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434)) = True.
Proof. exact (@lem1609542 (term293 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609544 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : ((term251 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434)) = True.
Proof. exact (TRANS (@lem1609539 _25435 _25436 _25433 _25434) (@lem1609543 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609545 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : True = ((term251 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434)).
Proof. exact (SYM (@lem1609544 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609546 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term251 _25435 _25436 _25433 _25434) = (term293 _25435 _25436 _25433 _25434).
Proof. exact (EQ_MP (@lem1609545 _25435 _25436 _25433 _25434) (@lem0)). Qed.
Lemma lem1609547 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : term293 _25435 _25436 _25433 _25434.
Proof. exact (EQ_MP (@lem1609546 _25435 _25436 _25433 _25434) (@lem1609251 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609549 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1609550 (_25433 : real) (_25434 : real) (_25435 : real) (_25436 : real) : (term293 _25435 _25436 _25433 _25434) = (term297 _25433 _25434 _25435 _25436).
Proof. exact (@lem1609549 (term298 _25435 _25436 _25433 _25434) (real_lt _25435 _25436)). Qed.
Lemma lem1609552 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609553 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term299 _25435 _25436 _25433 _25434) = (term300 _25435 _25436 _25433 _25434).
Proof. exact (@lem1609552 (term261 _25433 _25435) (term294 _25436 _25433 _25434)). Qed.
Lemma lem1609555 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609556 (_25433 : real) (_25435 : real) : (term276 _25433 _25435) = (_25433 = _25435).
Proof. exact (@lem1609555 (_25433 = _25435)). Qed.
Lemma lem1609557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609558 (_25433 : real) (_25435 : real) : (term277 _25433 _25435) = (term278 _25433 _25435).
Proof. exact (MK_COMB (@lem1609557) (@lem1609556 _25433 _25435)). Qed.
Lemma lem1609560 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609561 (_25436 : real) (_25433 : real) (_25434 : real) : (term301 _25436 _25433 _25434) = (term302 _25436 _25433 _25434).
Proof. exact (@lem1609560 (term261 _25434 _25436) (term291 _25433 _25434)). Qed.
Lemma lem1609563 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609564 (_25434 : real) (_25436 : real) : (term276 _25434 _25436) = (_25434 = _25436).
Proof. exact (@lem1609563 (_25434 = _25436)). Qed.
Lemma lem1609565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609566 (_25434 : real) (_25436 : real) : (term277 _25434 _25436) = (term278 _25434 _25436).
Proof. exact (MK_COMB (@lem1609565) (@lem1609564 _25434 _25436)). Qed.
Lemma lem1609568 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609569 (_25433 : real) (_25434 : real) : (term303 _25433 _25434) = (real_lt _25433 _25434).
Proof. exact (@lem1609568 (real_lt _25433 _25434)). Qed.
Lemma lem1609570 (_25436 : real) (_25433 : real) (_25434 : real) : (term302 _25436 _25433 _25434) = (term304 _25436 _25433 _25434).
Proof. exact (MK_COMB (@lem1609566 _25434 _25436) (@lem1609569 _25433 _25434)). Qed.
Lemma lem1609571 (_25436 : real) (_25433 : real) (_25434 : real) : (term301 _25436 _25433 _25434) = (term304 _25436 _25433 _25434).
Proof. exact (TRANS (@lem1609561 _25436 _25433 _25434) (@lem1609570 _25436 _25433 _25434)). Qed.
Lemma lem1609572 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term300 _25435 _25436 _25433 _25434) = (term305 _25435 _25436 _25433 _25434).
Proof. exact (MK_COMB (@lem1609558 _25433 _25435) (@lem1609571 _25436 _25433 _25434)). Qed.
Lemma lem1609573 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term299 _25435 _25436 _25433 _25434) = (term305 _25435 _25436 _25433 _25434).
Proof. exact (TRANS (@lem1609553 _25435 _25436 _25433 _25434) (@lem1609572 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609574 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1609575 (_25435 : real) (_25436 : real) (_25433 : real) (_25434 : real) : (term306 _25435 _25436 _25433 _25434) = (term307 _25435 _25436 _25433 _25434).
Proof. exact (MK_COMB (@lem1609574) (@lem1609573 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609576 (_25435 : real) (_25436 : real) : (real_lt _25435 _25436) = (real_lt _25435 _25436).
Proof. exact (eq_refl (real_lt _25435 _25436)). Qed.
Lemma lem1609577 (_25433 : real) (_25434 : real) (_25435 : real) (_25436 : real) : (term297 _25433 _25434 _25435 _25436) = (term308 _25433 _25434 _25435 _25436).
Proof. exact (MK_COMB (@lem1609575 _25435 _25436 _25433 _25434) (@lem1609576 _25435 _25436)). Qed.
Lemma lem1609578 (_25433 : real) (_25434 : real) (_25435 : real) (_25436 : real) : (term293 _25435 _25436 _25433 _25434) = (term308 _25433 _25434 _25435 _25436).
Proof. exact (TRANS (@lem1609550 _25433 _25434 _25435 _25436) (@lem1609577 _25433 _25434 _25435 _25436)). Qed.
Lemma lem1609580 (x : real) (y : real) (h1 : term34) (h2 : term129 x y) (h3 : term59 x y) : term363 x y.
Proof. exact (conj (@lem1609302 x y) (@lem1609433 x y h1 h2 h3)). Qed.
Lemma lem1609581 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : term364 x y.
Proof. exact (conj (@lem1609294 y h2) (@lem1609580 x y h1 h3 h4)). Qed.
Lemma lem1609583 (_25433 : real) (_25434 : real) (_25435 : real) (_25436 : real) : term308 _25433 _25434 _25435 _25436.
Proof. exact (EQ_MP (@lem1609578 _25433 _25434 _25435 _25436) (@lem1609547 _25435 _25436 _25433 _25434)). Qed.
Lemma lem1609584 (x : real) (y : real) : term365 x y.
Proof. exact (@lem1609583 (term35 y) (real_mul x y) term36 (real_mul x y)). Qed.
Lemma lem1609587 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : term55 x y.
Proof. exact (@lem1609584 x y (@lem1609581 x y h1 h2 h3 h4)). Qed.
Lemma lem1609588 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : term289 x y.
Proof. exact (fun h0 : term241 x y => @lem1609587 x y h1 h2 h3 h4). Qed.
Lemma lem1609590 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609591 (x : real) (y : real) : (term289 x y) = (term55 x y).
Proof. exact (@lem1609590 (term55 x y)). Qed.
Lemma lem1609592 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : term55 x y.
Proof. exact (EQ_MP (@lem1609591 x y) (@lem1609588 x y h1 h2 h3 h4)). Qed.
Lemma lem1609595 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1609597 (x : real) (y : real) : (term241 x y) = (term366 x y).
Proof. exact (@lem1609595 (term55 x y)). Qed.
Lemma lem1609600 (x : real) (y : real) (h1 : term129 x y) : term366 x y.
Proof. exact (EQ_MP (@lem1609597 x y) (@lem1608571 x y h1)). Qed.
Lemma lem1609603 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : False.
Proof. exact (@lem1609600 x y h3 (@lem1609592 x y h1 h2 h3 h4)). Qed.
Lemma lem1609604 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : term341.
Proof. exact (fun h0 : ~ False => @lem1609603 x y h1 h2 h3 h4). Qed.
Lemma lem1609606 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609607 : term341 = False.
Proof. exact (@lem1609606 False). Qed.
Lemma lem1609608 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : False.
Proof. exact (EQ_MP (@lem1609607) (@lem1609604 x y h1 h2 h3 h4)). Qed.
Lemma lem1609609 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1609610 (_25445 : real) (_25447 : real) (h1 : _25445 = _25447) : _25445 = _25447.
Proof. exact (h1). Qed.
Lemma lem1609611 (_25446 : real) (_25448 : real) (h1 : _25446 = _25448) : _25446 = _25448.
Proof. exact (h1). Qed.
Lemma lem1609612 (_25445 : real) (_25447 : real) (h1 : _25445 = _25447) : (real_lt _25445) = (real_lt _25447).
Proof. exact (MK_COMB (@lem1609609) (@lem1609610 _25445 _25447 h1)). Qed.
Lemma lem1609613 (_25445 : real) (_25447 : real) (_25446 : real) (_25448 : real) (h1 : _25445 = _25447) (h2 : _25446 = _25448) : (real_lt _25445 _25446) = (real_lt _25447 _25448).
Proof. exact (MK_COMB (@lem1609612 _25445 _25447 h1) (@lem1609611 _25446 _25448 h2)). Qed.
Lemma lem1609615 (b : Prop) (a : Prop) : term244 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1609616 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : term245 _25447 _25448 _25445 _25446.
Proof. exact (@lem1609615 (real_lt _25447 _25448) (real_lt _25445 _25446)). Qed.
Lemma lem1609617 (_25445 : real) (_25447 : real) (_25446 : real) (_25448 : real) (h1 : _25445 = _25447) (h2 : _25446 = _25448) : term246 _25447 _25448 _25445 _25446.
Proof. exact (@lem1609616 _25447 _25448 _25445 _25446 (@lem1609613 _25445 _25447 _25446 _25448 h1 h2)). Qed.
Lemma lem1609618 (_25448 : real) (_25446 : real) (_25445 : real) (_25447 : real) (h1 : _25445 = _25447) : term247 _25447 _25448 _25445 _25446.
Proof. exact (fun h0 : _25446 = _25448 => @lem1609617 _25445 _25447 _25446 _25448 h1 h0). Qed.
Lemma lem1609620 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1609621 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term247 _25447 _25448 _25445 _25446) = (term249 _25447 _25448 _25445 _25446).
Proof. exact (@lem1609620 (_25446 = _25448) (term246 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609622 (_25448 : real) (_25446 : real) (_25445 : real) (_25447 : real) (h1 : _25445 = _25447) : term249 _25447 _25448 _25445 _25446.
Proof. exact (EQ_MP (@lem1609621 _25447 _25448 _25445 _25446) (@lem1609618 _25448 _25446 _25445 _25447 h1)). Qed.
Lemma lem1609623 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : term250 _25447 _25448 _25445 _25446.
Proof. exact (fun h0 : _25445 = _25447 => @lem1609622 _25448 _25446 _25445 _25447 h0). Qed.
Lemma lem1609625 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1609626 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term250 _25447 _25448 _25445 _25446) = (term251 _25447 _25448 _25445 _25446).
Proof. exact (@lem1609625 (_25445 = _25447) (term249 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609627 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : term251 _25447 _25448 _25445 _25446.
Proof. exact (EQ_MP (@lem1609626 _25447 _25448 _25445 _25446) (@lem1609623 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609660 (x : real) (y : real) (z : real) : term252 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1609664 (y : real) (x : real) (h1 : term80 y x) : term56 y.
Proof. exact (proj1 (@lem1607953 y x h1)). Qed.
Lemma lem1609665 (y : real) (x : real) (h1 : term80 y x) : term253 y.
Proof. exact (fun h0 : term215 y => @lem1609664 y x h1). Qed.
Lemma lem1609667 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609668 (y : real) : (term253 y) = (term56 y).
Proof. exact (@lem1609667 (term56 y)). Qed.
Lemma lem1609669 (y : real) (x : real) (h1 : term80 y x) : term56 y.
Proof. exact (EQ_MP (@lem1609668 y) (@lem1609665 y x h1)). Qed.
Lemma lem1609671 (_25406 : real) (h1 : term38) : (term35 _25406) = term36.
Proof. exact (EQ_MP (@lem1608454 _25406) (@lem1608453 _25406 h1)). Qed.
Lemma lem1609672 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (@lem1609671 y h1). Qed.
Lemma lem1609673 (y : real) (h1 : term38) : term342 y.
Proof. exact (fun h0 : term343 y => @lem1609672 y h1). Qed.
Lemma lem1609675 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609676 (y : real) : (term342 y) = ((term35 y) = term36).
Proof. exact (@lem1609675 ((term35 y) = term36)). Qed.
Lemma lem1609677 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (EQ_MP (@lem1609676 y) (@lem1609673 y h1)). Qed.
Lemma lem1609679 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1609680 (y : real) : (term35 y) = (term35 y).
Proof. exact (@lem1609679 (term35 y)). Qed.
Lemma lem1609681 (y : real) : term367 y.
Proof. exact (fun h0 : term368 y => @lem1609680 y). Qed.
Lemma lem1609683 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609684 (y : real) : (term367 y) = ((term35 y) = (term35 y)).
Proof. exact (@lem1609683 ((term35 y) = (term35 y))). Qed.
Lemma lem1609685 (y : real) : (term35 y) = (term35 y).
Proof. exact (EQ_MP (@lem1609684 y) (@lem1609681 y)). Qed.
Lemma lem1609703 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1609704 (y : real) (x : real) (z : real) : (term259 x y z) = (term260 y x z).
Proof. exact (@lem1609703 (y = z) (term261 x z)). Qed.
Lemma lem1609714 (x : real) (y : real) : (term262 x y) = (term262 x y).
Proof. exact (eq_refl (term262 x y)). Qed.
Lemma lem1609715 (y : real) (x : real) (z : real) : (term252 x y z) = (term263 y x z).
Proof. exact (MK_COMB (@lem1609714 x y) (@lem1609704 y x z)). Qed.
Lemma lem1609719 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609720 (y : real) (x : real) (z : real) : (term263 y x z) = (term265 y x z).
Proof. exact (@lem1609719 (y = z) (term261 x y) (term261 x z)). Qed.
Lemma lem1609742 (y : real) (x : real) (z : real) : (term252 x y z) = (term265 y x z).
Proof. exact (TRANS (@lem1609715 y x z) (@lem1609720 y x z)). Qed.
Lemma lem1609743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1609744 (y : real) (x : real) (z : real) : (term266 x y z) = (term267 y x z).
Proof. exact (MK_COMB (@lem1609743) (@lem1609742 y x z)). Qed.
Lemma lem1609766 (y : real) (x : real) (z : real) : (term265 y x z) = (term265 y x z).
Proof. exact (eq_refl (term265 y x z)). Qed.
Lemma lem1609767 (y : real) (x : real) (z : real) : ((term252 x y z) = (term265 y x z)) = ((term265 y x z) = (term265 y x z)).
Proof. exact (MK_COMB (@lem1609744 y x z) (@lem1609766 y x z)). Qed.
Lemma lem1609769 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1609770 (x : Prop) : (x = x) = True.
Proof. exact (@lem1609769 Prop x). Qed.
Lemma lem1609771 (y : real) (x : real) (z : real) : ((term265 y x z) = (term265 y x z)) = True.
Proof. exact (@lem1609770 (term265 y x z)). Qed.
Lemma lem1609772 (y : real) (x : real) (z : real) : ((term252 x y z) = (term265 y x z)) = True.
Proof. exact (TRANS (@lem1609767 y x z) (@lem1609771 y x z)). Qed.
Lemma lem1609773 (y : real) (x : real) (z : real) : True = ((term252 x y z) = (term265 y x z)).
Proof. exact (SYM (@lem1609772 y x z)). Qed.
Lemma lem1609774 (y : real) (x : real) (z : real) : (term252 x y z) = (term265 y x z).
Proof. exact (EQ_MP (@lem1609773 y x z) (@lem0)). Qed.
Lemma lem1609775 (y : real) (x : real) (z : real) : term265 y x z.
Proof. exact (EQ_MP (@lem1609774 y x z) (@lem1609660 x y z)). Qed.
Lemma lem1609777 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1609778 (x : real) (y : real) (z : real) : (term265 y x z) = (term269 x y z).
Proof. exact (@lem1609777 (term270 y x z) (y = z)). Qed.
Lemma lem1609780 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609781 (y : real) (x : real) (z : real) : (term273 y x z) = (term274 y x z).
Proof. exact (@lem1609780 (term261 x y) (term261 x z)). Qed.
Lemma lem1609783 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609784 (x : real) (y : real) : (term276 x y) = (x = y).
Proof. exact (@lem1609783 (x = y)). Qed.
Lemma lem1609785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609786 (x : real) (y : real) : (term277 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1609785) (@lem1609784 x y)). Qed.
Lemma lem1609788 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609789 (x : real) (z : real) : (term276 x z) = (x = z).
Proof. exact (@lem1609788 (x = z)). Qed.
Lemma lem1609790 (y : real) (x : real) (z : real) : (term274 y x z) = (term279 y x z).
Proof. exact (MK_COMB (@lem1609786 x y) (@lem1609789 x z)). Qed.
Lemma lem1609791 (y : real) (x : real) (z : real) : (term273 y x z) = (term279 y x z).
Proof. exact (TRANS (@lem1609781 y x z) (@lem1609790 y x z)). Qed.
Lemma lem1609792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1609793 (y : real) (x : real) (z : real) : (term280 y x z) = (term281 y x z).
Proof. exact (MK_COMB (@lem1609792) (@lem1609791 y x z)). Qed.
Lemma lem1609794 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1609795 (x : real) (y : real) (z : real) : (term269 x y z) = (term282 x y z).
Proof. exact (MK_COMB (@lem1609793 y x z) (@lem1609794 y z)). Qed.
Lemma lem1609796 (x : real) (y : real) (z : real) : (term265 y x z) = (term282 x y z).
Proof. exact (TRANS (@lem1609778 x y z) (@lem1609795 x y z)). Qed.
Lemma lem1609798 (y : real) (h1 : term38) : term369 y.
Proof. exact (conj (@lem1609677 y h1) (@lem1609685 y)). Qed.
Lemma lem1609800 (x : real) (y : real) (z : real) : term282 x y z.
Proof. exact (EQ_MP (@lem1609796 x y z) (@lem1609775 y x z)). Qed.
Lemma lem1609801 (y : real) : term370 y.
Proof. exact (@lem1609800 (term35 y) term36 (term35 y)). Qed.
Lemma lem1609804 (y : real) (h1 : term38) : term36 = (term35 y).
Proof. exact (@lem1609801 y (@lem1609798 y h1)). Qed.
Lemma lem1609805 (y : real) (h1 : term38) : term371 y.
Proof. exact (fun h0 : term372 y => @lem1609804 y h1). Qed.
Lemma lem1609807 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609808 (y : real) : (term371 y) = (term36 = (term35 y)).
Proof. exact (@lem1609807 (term36 = (term35 y))). Qed.
Lemma lem1609809 (y : real) (h1 : term38) : term36 = (term35 y).
Proof. exact (EQ_MP (@lem1609808 y) (@lem1609805 y h1)). Qed.
Lemma lem1609811 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1609812 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1609811 (real_mul x y)). Qed.
Lemma lem1609813 (x : real) (y : real) : term287 x y.
Proof. exact (fun h0 : term288 x y => @lem1609812 x y). Qed.
Lemma lem1609815 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609816 (x : real) (y : real) : (term287 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1609815 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1609817 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1609816 x y) (@lem1609813 x y)). Qed.
Lemma lem1609819 (y : real) (x : real) (h1 : term211 y x) : term55 x y.
Proof. exact (proj1 (@lem1607964 y x h1)). Qed.
Lemma lem1609820 (y : real) (x : real) (h1 : term211 y x) : term289 x y.
Proof. exact (fun h0 : term241 x y => @lem1609819 y x h1). Qed.
Lemma lem1609822 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609823 (x : real) (y : real) : (term289 x y) = (term55 x y).
Proof. exact (@lem1609822 (term55 x y)). Qed.
Lemma lem1609824 (y : real) (x : real) (h1 : term211 y x) : term55 x y.
Proof. exact (EQ_MP (@lem1609823 x y) (@lem1609820 y x h1)). Qed.
Lemma lem1609842 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609843 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term249 _25447 _25448 _25445 _25446) = (term290 _25447 _25448 _25445 _25446).
Proof. exact (@lem1609842 (real_lt _25447 _25448) (term261 _25446 _25448) (term291 _25445 _25446)). Qed.
Lemma lem1609861 (_25445 : real) (_25447 : real) : (term262 _25445 _25447) = (term262 _25445 _25447).
Proof. exact (eq_refl (term262 _25445 _25447)). Qed.
Lemma lem1609862 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term251 _25447 _25448 _25445 _25446) = (term292 _25447 _25448 _25445 _25446).
Proof. exact (MK_COMB (@lem1609861 _25445 _25447) (@lem1609843 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609866 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609867 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term292 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446).
Proof. exact (@lem1609866 (real_lt _25447 _25448) (term261 _25445 _25447) (term294 _25448 _25445 _25446)). Qed.
Lemma lem1609897 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term251 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446).
Proof. exact (TRANS (@lem1609862 _25447 _25448 _25445 _25446) (@lem1609867 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1609899 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term295 _25447 _25448 _25445 _25446) = (term296 _25447 _25448 _25445 _25446).
Proof. exact (MK_COMB (@lem1609898) (@lem1609897 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609929 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term293 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446).
Proof. exact (eq_refl (term293 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609930 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : ((term251 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446)) = ((term293 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446)).
Proof. exact (MK_COMB (@lem1609899 _25447 _25448 _25445 _25446) (@lem1609929 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1609933 (x : Prop) : (x = x) = True.
Proof. exact (@lem1609932 Prop x). Qed.
Lemma lem1609934 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : ((term293 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446)) = True.
Proof. exact (@lem1609933 (term293 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609935 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : ((term251 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446)) = True.
Proof. exact (TRANS (@lem1609930 _25447 _25448 _25445 _25446) (@lem1609934 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609936 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : True = ((term251 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446)).
Proof. exact (SYM (@lem1609935 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609937 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term251 _25447 _25448 _25445 _25446) = (term293 _25447 _25448 _25445 _25446).
Proof. exact (EQ_MP (@lem1609936 _25447 _25448 _25445 _25446) (@lem0)). Qed.
Lemma lem1609938 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : term293 _25447 _25448 _25445 _25446.
Proof. exact (EQ_MP (@lem1609937 _25447 _25448 _25445 _25446) (@lem1609627 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609940 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1609941 (_25445 : real) (_25446 : real) (_25447 : real) (_25448 : real) : (term293 _25447 _25448 _25445 _25446) = (term297 _25445 _25446 _25447 _25448).
Proof. exact (@lem1609940 (term298 _25447 _25448 _25445 _25446) (real_lt _25447 _25448)). Qed.
Lemma lem1609943 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609944 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term299 _25447 _25448 _25445 _25446) = (term300 _25447 _25448 _25445 _25446).
Proof. exact (@lem1609943 (term261 _25445 _25447) (term294 _25448 _25445 _25446)). Qed.
Lemma lem1609946 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609947 (_25445 : real) (_25447 : real) : (term276 _25445 _25447) = (_25445 = _25447).
Proof. exact (@lem1609946 (_25445 = _25447)). Qed.
Lemma lem1609948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609949 (_25445 : real) (_25447 : real) : (term277 _25445 _25447) = (term278 _25445 _25447).
Proof. exact (MK_COMB (@lem1609948) (@lem1609947 _25445 _25447)). Qed.
Lemma lem1609951 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1609952 (_25448 : real) (_25445 : real) (_25446 : real) : (term301 _25448 _25445 _25446) = (term302 _25448 _25445 _25446).
Proof. exact (@lem1609951 (term261 _25446 _25448) (term291 _25445 _25446)). Qed.
Lemma lem1609954 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609955 (_25446 : real) (_25448 : real) : (term276 _25446 _25448) = (_25446 = _25448).
Proof. exact (@lem1609954 (_25446 = _25448)). Qed.
Lemma lem1609956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1609957 (_25446 : real) (_25448 : real) : (term277 _25446 _25448) = (term278 _25446 _25448).
Proof. exact (MK_COMB (@lem1609956) (@lem1609955 _25446 _25448)). Qed.
Lemma lem1609959 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1609960 (_25445 : real) (_25446 : real) : (term303 _25445 _25446) = (real_lt _25445 _25446).
Proof. exact (@lem1609959 (real_lt _25445 _25446)). Qed.
Lemma lem1609961 (_25448 : real) (_25445 : real) (_25446 : real) : (term302 _25448 _25445 _25446) = (term304 _25448 _25445 _25446).
Proof. exact (MK_COMB (@lem1609957 _25446 _25448) (@lem1609960 _25445 _25446)). Qed.
Lemma lem1609962 (_25448 : real) (_25445 : real) (_25446 : real) : (term301 _25448 _25445 _25446) = (term304 _25448 _25445 _25446).
Proof. exact (TRANS (@lem1609952 _25448 _25445 _25446) (@lem1609961 _25448 _25445 _25446)). Qed.
Lemma lem1609963 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term300 _25447 _25448 _25445 _25446) = (term305 _25447 _25448 _25445 _25446).
Proof. exact (MK_COMB (@lem1609949 _25445 _25447) (@lem1609962 _25448 _25445 _25446)). Qed.
Lemma lem1609964 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term299 _25447 _25448 _25445 _25446) = (term305 _25447 _25448 _25445 _25446).
Proof. exact (TRANS (@lem1609944 _25447 _25448 _25445 _25446) (@lem1609963 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1609966 (_25447 : real) (_25448 : real) (_25445 : real) (_25446 : real) : (term306 _25447 _25448 _25445 _25446) = (term307 _25447 _25448 _25445 _25446).
Proof. exact (MK_COMB (@lem1609965) (@lem1609964 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609967 (_25447 : real) (_25448 : real) : (real_lt _25447 _25448) = (real_lt _25447 _25448).
Proof. exact (eq_refl (real_lt _25447 _25448)). Qed.
Lemma lem1609968 (_25445 : real) (_25446 : real) (_25447 : real) (_25448 : real) : (term297 _25445 _25446 _25447 _25448) = (term308 _25445 _25446 _25447 _25448).
Proof. exact (MK_COMB (@lem1609966 _25447 _25448 _25445 _25446) (@lem1609967 _25447 _25448)). Qed.
Lemma lem1609969 (_25445 : real) (_25446 : real) (_25447 : real) (_25448 : real) : (term293 _25447 _25448 _25445 _25446) = (term308 _25445 _25446 _25447 _25448).
Proof. exact (TRANS (@lem1609941 _25445 _25446 _25447 _25448) (@lem1609968 _25445 _25446 _25447 _25448)). Qed.
Lemma lem1609971 (y : real) (x : real) (h1 : term211 y x) : term309 x y.
Proof. exact (conj (@lem1609817 x y) (@lem1609824 y x h1)). Qed.
Lemma lem1609972 (y : real) (x : real) (h1 : term38) (h2 : term211 y x) : term373 x y.
Proof. exact (conj (@lem1609809 y h1) (@lem1609971 y x h2)). Qed.
Lemma lem1609974 (_25445 : real) (_25446 : real) (_25447 : real) (_25448 : real) : term308 _25445 _25446 _25447 _25448.
Proof. exact (EQ_MP (@lem1609969 _25445 _25446 _25447 _25448) (@lem1609938 _25447 _25448 _25445 _25446)). Qed.
Lemma lem1609975 (x : real) (y : real) : term374 x y.
Proof. exact (@lem1609974 term36 (real_mul x y) (term35 y) (real_mul x y)). Qed.
Lemma lem1609978 (y : real) (x : real) (h1 : term38) (h2 : term211 y x) : term360 x y.
Proof. exact (@lem1609975 x y (@lem1609972 y x h1 h2)). Qed.
Lemma lem1609979 (y : real) (x : real) (h1 : term38) (h2 : term211 y x) : term361 x y.
Proof. exact (fun h0 : term362 x y => @lem1609978 y x h1 h2). Qed.
Lemma lem1609981 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1609982 (x : real) (y : real) : (term361 x y) = (term360 x y).
Proof. exact (@lem1609981 (term360 x y)). Qed.
Lemma lem1609983 (y : real) (x : real) (h1 : term38) (h2 : term211 y x) : term360 x y.
Proof. exact (EQ_MP (@lem1609982 x y) (@lem1609979 y x h1 h2)). Qed.
Lemma lem1609989 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1609990 (_25409 : real) (_25407 : real) (_25408 : real) : (term243 _25409 _25407 _25408) = (term375 _25409 _25407 _25408).
Proof. exact (@lem1609989 (term376 _25407 _25408 _25409) (term215 _25409) (real_lt _25407 _25408)). Qed.
Lemma lem1610004 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1610005 (_25407 : real) (_25408 : real) (_25409 : real) : (term317 _25409 _25407 _25408) = (term318 _25407 _25408 _25409).
Proof. exact (@lem1610004 (real_lt _25407 _25408) (term215 _25409)). Qed.
Lemma lem1610011 (_25407 : real) (_25408 : real) (_25409 : real) : (term377 _25407 _25408 _25409) = (term377 _25407 _25408 _25409).
Proof. exact (eq_refl (term377 _25407 _25408 _25409)). Qed.
Lemma lem1610012 (_25407 : real) (_25408 : real) (_25409 : real) : (term375 _25409 _25407 _25408) = (term378 _25407 _25408 _25409).
Proof. exact (MK_COMB (@lem1610011 _25407 _25408 _25409) (@lem1610005 _25407 _25408 _25409)). Qed.
Lemma lem1610016 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1610017 (_25407 : real) (_25408 : real) (_25409 : real) : (term378 _25407 _25408 _25409) = (term379 _25407 _25408 _25409).
Proof. exact (@lem1610016 (real_lt _25407 _25408) (term376 _25407 _25408 _25409) (term215 _25409)). Qed.
Lemma lem1610033 (_25407 : real) (_25408 : real) (_25409 : real) : (term375 _25409 _25407 _25408) = (term379 _25407 _25408 _25409).
Proof. exact (TRANS (@lem1610012 _25407 _25408 _25409) (@lem1610017 _25407 _25408 _25409)). Qed.
Lemma lem1610034 (_25407 : real) (_25408 : real) (_25409 : real) : (term243 _25409 _25407 _25408) = (term379 _25407 _25408 _25409).
Proof. exact (TRANS (@lem1609990 _25409 _25407 _25408) (@lem1610033 _25407 _25408 _25409)). Qed.
Lemma lem1610035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610036 (_25407 : real) (_25408 : real) (_25409 : real) : (term380 _25409 _25407 _25408) = (term381 _25407 _25408 _25409).
Proof. exact (MK_COMB (@lem1610035) (@lem1610034 _25407 _25408 _25409)). Qed.
Lemma lem1610050 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1610051 (_25407 : real) (_25408 : real) (_25409 : real) : (term382 _25407 _25408 _25409) = (term383 _25407 _25408 _25409).
Proof. exact (@lem1610050 (term376 _25407 _25408 _25409) (term215 _25409)). Qed.
Lemma lem1610057 (_25407 : real) (_25408 : real) : (term326 _25407 _25408) = (term326 _25407 _25408).
Proof. exact (eq_refl (term326 _25407 _25408)). Qed.
Lemma lem1610058 (_25407 : real) (_25408 : real) (_25409 : real) : (term384 _25407 _25408 _25409) = (term379 _25407 _25408 _25409).
Proof. exact (MK_COMB (@lem1610057 _25407 _25408) (@lem1610051 _25407 _25408 _25409)). Qed.
Lemma lem1610069 (_25407 : real) (_25408 : real) (_25409 : real) : ((term243 _25409 _25407 _25408) = (term384 _25407 _25408 _25409)) = ((term379 _25407 _25408 _25409) = (term379 _25407 _25408 _25409)).
Proof. exact (MK_COMB (@lem1610036 _25407 _25408 _25409) (@lem1610058 _25407 _25408 _25409)). Qed.
Lemma lem1610071 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1610072 (x : Prop) : (x = x) = True.
Proof. exact (@lem1610071 Prop x). Qed.
Lemma lem1610073 (_25407 : real) (_25408 : real) (_25409 : real) : ((term379 _25407 _25408 _25409) = (term379 _25407 _25408 _25409)) = True.
Proof. exact (@lem1610072 (term379 _25407 _25408 _25409)). Qed.
Lemma lem1610074 (_25407 : real) (_25408 : real) (_25409 : real) : ((term243 _25409 _25407 _25408) = (term384 _25407 _25408 _25409)) = True.
Proof. exact (TRANS (@lem1610069 _25407 _25408 _25409) (@lem1610073 _25407 _25408 _25409)). Qed.
Lemma lem1610075 (_25407 : real) (_25408 : real) (_25409 : real) : True = ((term243 _25409 _25407 _25408) = (term384 _25407 _25408 _25409)).
Proof. exact (SYM (@lem1610074 _25407 _25408 _25409)). Qed.
Lemma lem1610076 (_25407 : real) (_25408 : real) (_25409 : real) : (term243 _25409 _25407 _25408) = (term384 _25407 _25408 _25409).
Proof. exact (EQ_MP (@lem1610075 _25407 _25408 _25409) (@lem0)). Qed.
Lemma lem1610077 (_25407 : real) (_25408 : real) (_25409 : real) (h1 : term34) : term384 _25407 _25408 _25409.
Proof. exact (EQ_MP (@lem1610076 _25407 _25408 _25409) (@lem1608663 _25409 _25407 _25408 h1)). Qed.
Lemma lem1610079 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1610080 (_25409 : real) (_25407 : real) (_25408 : real) : (term384 _25407 _25408 _25409) = (term385 _25409 _25407 _25408).
Proof. exact (@lem1610079 (term382 _25407 _25408 _25409) (real_lt _25407 _25408)). Qed.
Lemma lem1610082 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1610083 (_25407 : real) (_25408 : real) (_25409 : real) : (term386 _25407 _25408 _25409) = (term387 _25407 _25408 _25409).
Proof. exact (@lem1610082 (term215 _25409) (term376 _25407 _25408 _25409)). Qed.
Lemma lem1610085 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610086 (_25409 : real) : (term331 _25409) = (term56 _25409).
Proof. exact (@lem1610085 (term56 _25409)). Qed.
Lemma lem1610087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610088 (_25409 : real) : (term332 _25409) = (term57 _25409).
Proof. exact (MK_COMB (@lem1610087) (@lem1610086 _25409)). Qed.
Lemma lem1610090 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610091 (_25407 : real) (_25408 : real) (_25409 : real) : (term388 _25407 _25408 _25409) = (term190 _25407 _25408 _25409).
Proof. exact (@lem1610090 (term190 _25407 _25408 _25409)). Qed.
Lemma lem1610092 (_25407 : real) (_25408 : real) (_25409 : real) : (term387 _25407 _25408 _25409) = (term389 _25407 _25408 _25409).
Proof. exact (MK_COMB (@lem1610088 _25409) (@lem1610091 _25407 _25408 _25409)). Qed.
Lemma lem1610093 (_25407 : real) (_25408 : real) (_25409 : real) : (term386 _25407 _25408 _25409) = (term389 _25407 _25408 _25409).
Proof. exact (TRANS (@lem1610083 _25407 _25408 _25409) (@lem1610092 _25407 _25408 _25409)). Qed.
Lemma lem1610094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1610095 (_25407 : real) (_25408 : real) (_25409 : real) : (term390 _25407 _25408 _25409) = (term391 _25407 _25408 _25409).
Proof. exact (MK_COMB (@lem1610094) (@lem1610093 _25407 _25408 _25409)). Qed.
Lemma lem1610096 (_25407 : real) (_25408 : real) : (real_lt _25407 _25408) = (real_lt _25407 _25408).
Proof. exact (eq_refl (real_lt _25407 _25408)). Qed.
Lemma lem1610097 (_25409 : real) (_25407 : real) (_25408 : real) : (term385 _25409 _25407 _25408) = (term392 _25409 _25407 _25408).
Proof. exact (MK_COMB (@lem1610095 _25407 _25408 _25409) (@lem1610096 _25407 _25408)). Qed.
Lemma lem1610098 (_25409 : real) (_25407 : real) (_25408 : real) : (term384 _25407 _25408 _25409) = (term392 _25409 _25407 _25408).
Proof. exact (TRANS (@lem1610080 _25409 _25407 _25408) (@lem1610097 _25409 _25407 _25408)). Qed.
Lemma lem1610100 (y : real) (x : real) (h1 : term38) (h2 : term80 y x) (h3 : term211 y x) : term393 x y.
Proof. exact (conj (@lem1609669 y x h2) (@lem1609983 y x h1 h3)). Qed.
Lemma lem1610102 (_25409 : real) (_25407 : real) (_25408 : real) (h1 : term34) : term392 _25409 _25407 _25408.
Proof. exact (EQ_MP (@lem1610098 _25409 _25407 _25408) (@lem1610077 _25407 _25408 _25409 h1)). Qed.
Lemma lem1610103 (y : real) (x : real) (h1 : term34) : term394 y x.
Proof. exact (@lem1610102 y term36 x h1). Qed.
Lemma lem1610106 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : term56 x.
Proof. exact (@lem1610103 y x h1 (@lem1610100 y x h2 h3 h4)). Qed.
Lemma lem1610107 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : term253 x.
Proof. exact (fun h0 : term215 x => @lem1610106 y x h1 h2 h3 h4). Qed.
Lemma lem1610109 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610110 (x : real) : (term253 x) = (term56 x).
Proof. exact (@lem1610109 (term56 x)). Qed.
Lemma lem1610111 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : term56 x.
Proof. exact (EQ_MP (@lem1610110 x) (@lem1610107 y x h1 h2 h3 h4)). Qed.
Lemma lem1610114 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1610116 (x : real) : (term215 x) = (term340 x).
Proof. exact (@lem1610114 (term56 x)). Qed.
Lemma lem1610119 (y : real) (x : real) (h1 : term211 y x) : term340 x.
Proof. exact (EQ_MP (@lem1610116 x) (@lem1608623 y x h1)). Qed.
Lemma lem1610122 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : False.
Proof. exact (@lem1610119 y x h4 (@lem1610111 y x h1 h2 h3 h4)). Qed.
Lemma lem1610123 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : term341.
Proof. exact (fun h0 : ~ False => @lem1610122 y x h1 h2 h3 h4). Qed.
Lemma lem1610125 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610126 : term341 = False.
Proof. exact (@lem1610125 False). Qed.
Lemma lem1610127 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : False.
Proof. exact (EQ_MP (@lem1610126) (@lem1610123 y x h1 h2 h3 h4)). Qed.
Lemma lem1610128 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1610129 (_25457 : real) (_25459 : real) (h1 : _25457 = _25459) : _25457 = _25459.
Proof. exact (h1). Qed.
Lemma lem1610130 (_25458 : real) (_25460 : real) (h1 : _25458 = _25460) : _25458 = _25460.
Proof. exact (h1). Qed.
Lemma lem1610131 (_25457 : real) (_25459 : real) (h1 : _25457 = _25459) : (real_lt _25457) = (real_lt _25459).
Proof. exact (MK_COMB (@lem1610128) (@lem1610129 _25457 _25459 h1)). Qed.
Lemma lem1610132 (_25457 : real) (_25459 : real) (_25458 : real) (_25460 : real) (h1 : _25457 = _25459) (h2 : _25458 = _25460) : (real_lt _25457 _25458) = (real_lt _25459 _25460).
Proof. exact (MK_COMB (@lem1610131 _25457 _25459 h1) (@lem1610130 _25458 _25460 h2)). Qed.
Lemma lem1610134 (b : Prop) (a : Prop) : term244 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1610135 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : term245 _25459 _25460 _25457 _25458.
Proof. exact (@lem1610134 (real_lt _25459 _25460) (real_lt _25457 _25458)). Qed.
Lemma lem1610136 (_25457 : real) (_25459 : real) (_25458 : real) (_25460 : real) (h1 : _25457 = _25459) (h2 : _25458 = _25460) : term246 _25459 _25460 _25457 _25458.
Proof. exact (@lem1610135 _25459 _25460 _25457 _25458 (@lem1610132 _25457 _25459 _25458 _25460 h1 h2)). Qed.
Lemma lem1610137 (_25460 : real) (_25458 : real) (_25457 : real) (_25459 : real) (h1 : _25457 = _25459) : term247 _25459 _25460 _25457 _25458.
Proof. exact (fun h0 : _25458 = _25460 => @lem1610136 _25457 _25459 _25458 _25460 h1 h0). Qed.
Lemma lem1610139 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1610140 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term247 _25459 _25460 _25457 _25458) = (term249 _25459 _25460 _25457 _25458).
Proof. exact (@lem1610139 (_25458 = _25460) (term246 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610141 (_25460 : real) (_25458 : real) (_25457 : real) (_25459 : real) (h1 : _25457 = _25459) : term249 _25459 _25460 _25457 _25458.
Proof. exact (EQ_MP (@lem1610140 _25459 _25460 _25457 _25458) (@lem1610137 _25460 _25458 _25457 _25459 h1)). Qed.
Lemma lem1610142 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : term250 _25459 _25460 _25457 _25458.
Proof. exact (fun h0 : _25457 = _25459 => @lem1610141 _25460 _25458 _25457 _25459 h0). Qed.
Lemma lem1610144 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1610145 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term250 _25459 _25460 _25457 _25458) = (term251 _25459 _25460 _25457 _25458).
Proof. exact (@lem1610144 (_25457 = _25459) (term249 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610146 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : term251 _25459 _25460 _25457 _25458.
Proof. exact (EQ_MP (@lem1610145 _25459 _25460 _25457 _25458) (@lem1610142 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610183 (_25414 : real) (h1 : term38) : (term35 _25414) = term36.
Proof. exact (EQ_MP (@lem1608478 _25414) (@lem1608477 _25414 h1)). Qed.
Lemma lem1610184 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (@lem1610183 y h1). Qed.
Lemma lem1610185 (y : real) (h1 : term38) : term342 y.
Proof. exact (fun h0 : term343 y => @lem1610184 y h1). Qed.
Lemma lem1610187 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610188 (y : real) : (term342 y) = ((term35 y) = term36).
Proof. exact (@lem1610187 ((term35 y) = term36)). Qed.
Lemma lem1610189 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (EQ_MP (@lem1610188 y) (@lem1610185 y h1)). Qed.
Lemma lem1610191 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1610192 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1610191 (real_mul x y)). Qed.
Lemma lem1610193 (x : real) (y : real) : term287 x y.
Proof. exact (fun h0 : term288 x y => @lem1610192 x y). Qed.
Lemma lem1610195 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610196 (x : real) (y : real) : (term287 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1610195 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1610197 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1610196 x y) (@lem1610193 x y)). Qed.
Lemma lem1610199 (y : real) (x : real) (h1 : term80 y x) : term56 y.
Proof. exact (proj1 (@lem1607953 y x h1)). Qed.
Lemma lem1610200 (y : real) (x : real) (h1 : term80 y x) : term253 y.
Proof. exact (fun h0 : term215 y => @lem1610199 y x h1). Qed.
Lemma lem1610202 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610203 (y : real) : (term253 y) = (term56 y).
Proof. exact (@lem1610202 (term56 y)). Qed.
Lemma lem1610204 (y : real) (x : real) (h1 : term80 y x) : term56 y.
Proof. exact (EQ_MP (@lem1610203 y) (@lem1610200 y x h1)). Qed.
Lemma lem1610206 (y : real) (x : real) (h1 : term212 y x) : term56 x.
Proof. exact (proj2 (@lem1607965 y x h1)). Qed.
Lemma lem1610207 (y : real) (x : real) (h1 : term212 y x) : term253 x.
Proof. exact (fun h0 : term215 x => @lem1610206 y x h1). Qed.
Lemma lem1610209 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610210 (x : real) : (term253 x) = (term56 x).
Proof. exact (@lem1610209 (term56 x)). Qed.
Lemma lem1610211 (y : real) (x : real) (h1 : term212 y x) : term56 x.
Proof. exact (EQ_MP (@lem1610210 x) (@lem1610207 y x h1)). Qed.
Lemma lem1610217 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1610218 (_25417 : real) (_25415 : real) (_25416 : real) : (term242 _25417 _25415 _25416) = (term344 _25417 _25415 _25416).
Proof. exact (@lem1610217 (term190 _25415 _25416 _25417) (term215 _25417) (term291 _25415 _25416)). Qed.
Lemma lem1610232 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1610233 (_25415 : real) (_25416 : real) (_25417 : real) : (term345 _25417 _25415 _25416) = (term346 _25415 _25416 _25417).
Proof. exact (@lem1610232 (term291 _25415 _25416) (term215 _25417)). Qed.
Lemma lem1610239 (_25415 : real) (_25416 : real) (_25417 : real) : (term347 _25415 _25416 _25417) = (term347 _25415 _25416 _25417).
Proof. exact (eq_refl (term347 _25415 _25416 _25417)). Qed.
Lemma lem1610240 (_25415 : real) (_25416 : real) (_25417 : real) : (term344 _25417 _25415 _25416) = (term348 _25415 _25416 _25417).
Proof. exact (MK_COMB (@lem1610239 _25415 _25416 _25417) (@lem1610233 _25415 _25416 _25417)). Qed.
Lemma lem1610251 (_25415 : real) (_25416 : real) (_25417 : real) : (term242 _25417 _25415 _25416) = (term348 _25415 _25416 _25417).
Proof. exact (TRANS (@lem1610218 _25417 _25415 _25416) (@lem1610240 _25415 _25416 _25417)). Qed.
Lemma lem1610252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610253 (_25415 : real) (_25416 : real) (_25417 : real) : (term349 _25417 _25415 _25416) = (term350 _25415 _25416 _25417).
Proof. exact (MK_COMB (@lem1610252) (@lem1610251 _25415 _25416 _25417)). Qed.
Lemma lem1610267 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1610268 (_25415 : real) (_25416 : real) (_25417 : real) : (term345 _25417 _25415 _25416) = (term346 _25415 _25416 _25417).
Proof. exact (@lem1610267 (term291 _25415 _25416) (term215 _25417)). Qed.
Lemma lem1610274 (_25415 : real) (_25416 : real) (_25417 : real) : (term347 _25415 _25416 _25417) = (term347 _25415 _25416 _25417).
Proof. exact (eq_refl (term347 _25415 _25416 _25417)). Qed.
Lemma lem1610275 (_25415 : real) (_25416 : real) (_25417 : real) : (term344 _25417 _25415 _25416) = (term348 _25415 _25416 _25417).
Proof. exact (MK_COMB (@lem1610274 _25415 _25416 _25417) (@lem1610268 _25415 _25416 _25417)). Qed.
Lemma lem1610286 (_25415 : real) (_25416 : real) (_25417 : real) : ((term242 _25417 _25415 _25416) = (term344 _25417 _25415 _25416)) = ((term348 _25415 _25416 _25417) = (term348 _25415 _25416 _25417)).
Proof. exact (MK_COMB (@lem1610253 _25415 _25416 _25417) (@lem1610275 _25415 _25416 _25417)). Qed.
Lemma lem1610288 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1610289 (x : Prop) : (x = x) = True.
Proof. exact (@lem1610288 Prop x). Qed.
Lemma lem1610290 (_25415 : real) (_25416 : real) (_25417 : real) : ((term348 _25415 _25416 _25417) = (term348 _25415 _25416 _25417)) = True.
Proof. exact (@lem1610289 (term348 _25415 _25416 _25417)). Qed.
Lemma lem1610291 (_25417 : real) (_25415 : real) (_25416 : real) : ((term242 _25417 _25415 _25416) = (term344 _25417 _25415 _25416)) = True.
Proof. exact (TRANS (@lem1610286 _25415 _25416 _25417) (@lem1610290 _25415 _25416 _25417)). Qed.
Lemma lem1610292 (_25417 : real) (_25415 : real) (_25416 : real) : True = ((term242 _25417 _25415 _25416) = (term344 _25417 _25415 _25416)).
Proof. exact (SYM (@lem1610291 _25417 _25415 _25416)). Qed.
Lemma lem1610293 (_25417 : real) (_25415 : real) (_25416 : real) : (term242 _25417 _25415 _25416) = (term344 _25417 _25415 _25416).
Proof. exact (EQ_MP (@lem1610292 _25417 _25415 _25416) (@lem0)). Qed.
Lemma lem1610294 (_25417 : real) (_25415 : real) (_25416 : real) (h1 : term34) : term344 _25417 _25415 _25416.
Proof. exact (EQ_MP (@lem1610293 _25417 _25415 _25416) (@lem1608703 _25417 _25415 _25416 h1)). Qed.
Lemma lem1610296 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1610297 (_25415 : real) (_25416 : real) (_25417 : real) : (term344 _25417 _25415 _25416) = (term351 _25415 _25416 _25417).
Proof. exact (@lem1610296 (term345 _25417 _25415 _25416) (term190 _25415 _25416 _25417)). Qed.
Lemma lem1610299 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1610300 (_25417 : real) (_25415 : real) (_25416 : real) : (term352 _25417 _25415 _25416) = (term353 _25417 _25415 _25416).
Proof. exact (@lem1610299 (term215 _25417) (term291 _25415 _25416)). Qed.
Lemma lem1610302 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610303 (_25417 : real) : (term331 _25417) = (term56 _25417).
Proof. exact (@lem1610302 (term56 _25417)). Qed.
Lemma lem1610304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610305 (_25417 : real) : (term332 _25417) = (term57 _25417).
Proof. exact (MK_COMB (@lem1610304) (@lem1610303 _25417)). Qed.
Lemma lem1610307 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610308 (_25415 : real) (_25416 : real) : (term303 _25415 _25416) = (real_lt _25415 _25416).
Proof. exact (@lem1610307 (real_lt _25415 _25416)). Qed.
Lemma lem1610309 (_25417 : real) (_25415 : real) (_25416 : real) : (term353 _25417 _25415 _25416) = (term354 _25417 _25415 _25416).
Proof. exact (MK_COMB (@lem1610305 _25417) (@lem1610308 _25415 _25416)). Qed.
Lemma lem1610310 (_25417 : real) (_25415 : real) (_25416 : real) : (term352 _25417 _25415 _25416) = (term354 _25417 _25415 _25416).
Proof. exact (TRANS (@lem1610300 _25417 _25415 _25416) (@lem1610309 _25417 _25415 _25416)). Qed.
Lemma lem1610311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1610312 (_25417 : real) (_25415 : real) (_25416 : real) : (term355 _25417 _25415 _25416) = (term356 _25417 _25415 _25416).
Proof. exact (MK_COMB (@lem1610311) (@lem1610310 _25417 _25415 _25416)). Qed.
Lemma lem1610313 (_25415 : real) (_25416 : real) (_25417 : real) : (term190 _25415 _25416 _25417) = (term190 _25415 _25416 _25417).
Proof. exact (eq_refl (term190 _25415 _25416 _25417)). Qed.
Lemma lem1610314 (_25415 : real) (_25416 : real) (_25417 : real) : (term351 _25415 _25416 _25417) = (term357 _25415 _25416 _25417).
Proof. exact (MK_COMB (@lem1610312 _25417 _25415 _25416) (@lem1610313 _25415 _25416 _25417)). Qed.
Lemma lem1610315 (_25415 : real) (_25416 : real) (_25417 : real) : (term344 _25417 _25415 _25416) = (term357 _25415 _25416 _25417).
Proof. exact (TRANS (@lem1610297 _25415 _25416 _25417) (@lem1610314 _25415 _25416 _25417)). Qed.
Lemma lem1610317 (y : real) (x : real) (h1 : term212 y x) (h2 : term80 y x) : term358 y x.
Proof. exact (conj (@lem1610204 y x h2) (@lem1610211 y x h1)). Qed.
Lemma lem1610319 (_25415 : real) (_25416 : real) (_25417 : real) (h1 : term34) : term357 _25415 _25416 _25417.
Proof. exact (EQ_MP (@lem1610315 _25415 _25416 _25417) (@lem1610294 _25417 _25415 _25416 h1)). Qed.
Lemma lem1610320 (x : real) (y : real) (h1 : term34) : term359 x y.
Proof. exact (@lem1610319 term36 x y h1). Qed.
Lemma lem1610323 (y : real) (x : real) (h1 : term34) (h2 : term212 y x) (h3 : term80 y x) : term360 x y.
Proof. exact (@lem1610320 x y h1 (@lem1610317 y x h2 h3)). Qed.
Lemma lem1610324 (y : real) (x : real) (h1 : term34) (h2 : term212 y x) (h3 : term80 y x) : term361 x y.
Proof. exact (fun h0 : term362 x y => @lem1610323 y x h1 h2 h3). Qed.
Lemma lem1610326 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610327 (x : real) (y : real) : (term361 x y) = (term360 x y).
Proof. exact (@lem1610326 (term360 x y)). Qed.
Lemma lem1610328 (y : real) (x : real) (h1 : term34) (h2 : term212 y x) (h3 : term80 y x) : term360 x y.
Proof. exact (EQ_MP (@lem1610327 x y) (@lem1610324 y x h1 h2 h3)). Qed.
Lemma lem1610346 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1610347 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term249 _25459 _25460 _25457 _25458) = (term290 _25459 _25460 _25457 _25458).
Proof. exact (@lem1610346 (real_lt _25459 _25460) (term261 _25458 _25460) (term291 _25457 _25458)). Qed.
Lemma lem1610365 (_25457 : real) (_25459 : real) : (term262 _25457 _25459) = (term262 _25457 _25459).
Proof. exact (eq_refl (term262 _25457 _25459)). Qed.
Lemma lem1610366 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term251 _25459 _25460 _25457 _25458) = (term292 _25459 _25460 _25457 _25458).
Proof. exact (MK_COMB (@lem1610365 _25457 _25459) (@lem1610347 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610370 (q : Prop) (p : Prop) (r : Prop) : (term264 p q r) = (term264 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1610371 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term292 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458).
Proof. exact (@lem1610370 (real_lt _25459 _25460) (term261 _25457 _25459) (term294 _25460 _25457 _25458)). Qed.
Lemma lem1610401 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term251 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458).
Proof. exact (TRANS (@lem1610366 _25459 _25460 _25457 _25458) (@lem1610371 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610403 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term295 _25459 _25460 _25457 _25458) = (term296 _25459 _25460 _25457 _25458).
Proof. exact (MK_COMB (@lem1610402) (@lem1610401 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610433 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term293 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458).
Proof. exact (eq_refl (term293 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610434 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : ((term251 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458)) = ((term293 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458)).
Proof. exact (MK_COMB (@lem1610403 _25459 _25460 _25457 _25458) (@lem1610433 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1610437 (x : Prop) : (x = x) = True.
Proof. exact (@lem1610436 Prop x). Qed.
Lemma lem1610438 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : ((term293 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458)) = True.
Proof. exact (@lem1610437 (term293 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610439 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : ((term251 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458)) = True.
Proof. exact (TRANS (@lem1610434 _25459 _25460 _25457 _25458) (@lem1610438 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610440 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : True = ((term251 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458)).
Proof. exact (SYM (@lem1610439 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610441 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term251 _25459 _25460 _25457 _25458) = (term293 _25459 _25460 _25457 _25458).
Proof. exact (EQ_MP (@lem1610440 _25459 _25460 _25457 _25458) (@lem0)). Qed.
Lemma lem1610442 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : term293 _25459 _25460 _25457 _25458.
Proof. exact (EQ_MP (@lem1610441 _25459 _25460 _25457 _25458) (@lem1610146 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610444 (b : Prop) (a : Prop) : (a \/ b) = (term268 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1610445 (_25457 : real) (_25458 : real) (_25459 : real) (_25460 : real) : (term293 _25459 _25460 _25457 _25458) = (term297 _25457 _25458 _25459 _25460).
Proof. exact (@lem1610444 (term298 _25459 _25460 _25457 _25458) (real_lt _25459 _25460)). Qed.
Lemma lem1610447 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1610448 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term299 _25459 _25460 _25457 _25458) = (term300 _25459 _25460 _25457 _25458).
Proof. exact (@lem1610447 (term261 _25457 _25459) (term294 _25460 _25457 _25458)). Qed.
Lemma lem1610450 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610451 (_25457 : real) (_25459 : real) : (term276 _25457 _25459) = (_25457 = _25459).
Proof. exact (@lem1610450 (_25457 = _25459)). Qed.
Lemma lem1610452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610453 (_25457 : real) (_25459 : real) : (term277 _25457 _25459) = (term278 _25457 _25459).
Proof. exact (MK_COMB (@lem1610452) (@lem1610451 _25457 _25459)). Qed.
Lemma lem1610455 (a : Prop) (b : Prop) : (term271 a b) = (term272 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1610456 (_25460 : real) (_25457 : real) (_25458 : real) : (term301 _25460 _25457 _25458) = (term302 _25460 _25457 _25458).
Proof. exact (@lem1610455 (term261 _25458 _25460) (term291 _25457 _25458)). Qed.
Lemma lem1610458 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610459 (_25458 : real) (_25460 : real) : (term276 _25458 _25460) = (_25458 = _25460).
Proof. exact (@lem1610458 (_25458 = _25460)). Qed.
Lemma lem1610460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610461 (_25458 : real) (_25460 : real) : (term277 _25458 _25460) = (term278 _25458 _25460).
Proof. exact (MK_COMB (@lem1610460) (@lem1610459 _25458 _25460)). Qed.
Lemma lem1610463 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1610464 (_25457 : real) (_25458 : real) : (term303 _25457 _25458) = (real_lt _25457 _25458).
Proof. exact (@lem1610463 (real_lt _25457 _25458)). Qed.
Lemma lem1610465 (_25460 : real) (_25457 : real) (_25458 : real) : (term302 _25460 _25457 _25458) = (term304 _25460 _25457 _25458).
Proof. exact (MK_COMB (@lem1610461 _25458 _25460) (@lem1610464 _25457 _25458)). Qed.
Lemma lem1610466 (_25460 : real) (_25457 : real) (_25458 : real) : (term301 _25460 _25457 _25458) = (term304 _25460 _25457 _25458).
Proof. exact (TRANS (@lem1610456 _25460 _25457 _25458) (@lem1610465 _25460 _25457 _25458)). Qed.
Lemma lem1610467 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term300 _25459 _25460 _25457 _25458) = (term305 _25459 _25460 _25457 _25458).
Proof. exact (MK_COMB (@lem1610453 _25457 _25459) (@lem1610466 _25460 _25457 _25458)). Qed.
Lemma lem1610468 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term299 _25459 _25460 _25457 _25458) = (term305 _25459 _25460 _25457 _25458).
Proof. exact (TRANS (@lem1610448 _25459 _25460 _25457 _25458) (@lem1610467 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1610470 (_25459 : real) (_25460 : real) (_25457 : real) (_25458 : real) : (term306 _25459 _25460 _25457 _25458) = (term307 _25459 _25460 _25457 _25458).
Proof. exact (MK_COMB (@lem1610469) (@lem1610468 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610471 (_25459 : real) (_25460 : real) : (real_lt _25459 _25460) = (real_lt _25459 _25460).
Proof. exact (eq_refl (real_lt _25459 _25460)). Qed.
Lemma lem1610472 (_25457 : real) (_25458 : real) (_25459 : real) (_25460 : real) : (term297 _25457 _25458 _25459 _25460) = (term308 _25457 _25458 _25459 _25460).
Proof. exact (MK_COMB (@lem1610470 _25459 _25460 _25457 _25458) (@lem1610471 _25459 _25460)). Qed.
Lemma lem1610473 (_25457 : real) (_25458 : real) (_25459 : real) (_25460 : real) : (term293 _25459 _25460 _25457 _25458) = (term308 _25457 _25458 _25459 _25460).
Proof. exact (TRANS (@lem1610445 _25457 _25458 _25459 _25460) (@lem1610472 _25457 _25458 _25459 _25460)). Qed.
Lemma lem1610475 (y : real) (x : real) (h1 : term34) (h2 : term212 y x) (h3 : term80 y x) : term363 x y.
Proof. exact (conj (@lem1610197 x y) (@lem1610328 y x h1 h2 h3)). Qed.
Lemma lem1610476 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : term364 x y.
Proof. exact (conj (@lem1610189 y h2) (@lem1610475 y x h1 h3 h4)). Qed.
Lemma lem1610478 (_25457 : real) (_25458 : real) (_25459 : real) (_25460 : real) : term308 _25457 _25458 _25459 _25460.
Proof. exact (EQ_MP (@lem1610473 _25457 _25458 _25459 _25460) (@lem1610442 _25459 _25460 _25457 _25458)). Qed.
Lemma lem1610479 (x : real) (y : real) : term365 x y.
Proof. exact (@lem1610478 (term35 y) (real_mul x y) term36 (real_mul x y)). Qed.
Lemma lem1610482 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : term55 x y.
Proof. exact (@lem1610479 x y (@lem1610476 y x h1 h2 h3 h4)). Qed.
Lemma lem1610483 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : term289 x y.
Proof. exact (fun h0 : term241 x y => @lem1610482 y x h1 h2 h3 h4). Qed.
Lemma lem1610485 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610486 (x : real) (y : real) : (term289 x y) = (term55 x y).
Proof. exact (@lem1610485 (term55 x y)). Qed.
Lemma lem1610487 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : term55 x y.
Proof. exact (EQ_MP (@lem1610486 x y) (@lem1610483 y x h1 h2 h3 h4)). Qed.
Lemma lem1610490 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1610492 (x : real) (y : real) : (term241 x y) = (term366 x y).
Proof. exact (@lem1610490 (term55 x y)). Qed.
Lemma lem1610495 (y : real) (x : real) (h1 : term212 y x) : term366 x y.
Proof. exact (EQ_MP (@lem1610492 x y) (@lem1608671 y x h1)). Qed.
Lemma lem1610498 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : False.
Proof. exact (@lem1610495 y x h3 (@lem1610487 y x h1 h2 h3 h4)). Qed.
Lemma lem1610499 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : term341.
Proof. exact (fun h0 : ~ False => @lem1610498 y x h1 h2 h3 h4). Qed.
Lemma lem1610501 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1610502 : term341 = False.
Proof. exact (@lem1610501 False). Qed.
Lemma lem1610503 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : False.
Proof. exact (EQ_MP (@lem1610502) (@lem1610499 y x h1 h2 h3 h4)). Qed.
Lemma lem1610504 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : term38 = False.
Proof. exact (prop_ext (fun h5 : term38 => @lem1610503 y x h1 h2 h3 h4) (fun h5 : False => @lem1608307 h2)). Qed.
Lemma lem1610505 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term80 y x) : False.
Proof. exact (EQ_MP (@lem1610504 y x h1 h2 h3 h4) (@lem1608307 h2)). Qed.
Lemma lem1610506 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : term38 = False.
Proof. exact (prop_ext (fun h5 : term38 => @lem1610127 y x h1 h2 h3 h4) (fun h5 : False => @lem1608199 h2)). Qed.
Lemma lem1610507 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) (h4 : term211 y x) : False.
Proof. exact (EQ_MP (@lem1610506 y x h1 h2 h3 h4) (@lem1608199 h2)). Qed.
Lemma lem1610508 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : term38 = False.
Proof. exact (prop_ext (fun h5 : term38 => @lem1609608 x y h1 h2 h3 h4) (fun h5 : False => @lem1608091 h2)). Qed.
Lemma lem1610509 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term129 x y) (h4 : term59 x y) : False.
Proof. exact (EQ_MP (@lem1610508 x y h1 h2 h3 h4) (@lem1608091 h2)). Qed.
Lemma lem1610510 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : term41 = False.
Proof. exact (prop_ext (fun h5 : term41 => @lem1609232 x y h1 h2 h3 h4) (fun h5 : False => @lem1607976 h2)). Qed.
Lemma lem1610511 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) (h4 : term125 x y) : False.
Proof. exact (EQ_MP (@lem1610510 x y h1 h2 h3 h4) (@lem1607976 h2)). Qed.
Lemma lem1610512 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term80 y x) : False.
Proof. exact (or_elim (@lem1607962 y x h3) (fun h0 : term211 y x => @lem1610507 y x h1 h2 h3 h0) (fun h0 : term212 y x => @lem1610505 y x h1 h2 h0 h3)). Qed.
Lemma lem1610513 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term59 x y) : False.
Proof. exact (or_elim (@lem1607954 x y h5) (fun h0 : term125 x y => @lem1610511 x y h1 h3 h5 h0) (fun h0 : term129 x y => @lem1610509 x y h2 h4 h0 h5)). Qed.
Lemma lem1610514 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : False.
Proof. exact (or_elim (@lem1607951 y x h5) (fun h0 : term59 x y => @lem1610513 x y h1 h2 h3 h4 h0) (fun h0 : term80 y x => @lem1610512 y x h2 h4 h0)). Qed.
Lemma lem1610515 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : (term184 y x) = False.
Proof. exact (prop_ext (fun h6 : term184 y x => @lem1610514 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1607951 y x h5)). Qed.
Lemma lem1610516 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : False.
Proof. exact (EQ_MP (@lem1610515 y x h1 h2 h3 h4 h5) (@lem1607951 y x h5)). Qed.
Lemma lem1610517 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1610516 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1607663 h4)). Qed.
Lemma lem1610518 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : False.
Proof. exact (EQ_MP (@lem1610517 y x h1 h2 h3 h4 h5) (@lem1607663 h4)). Qed.
Lemma lem1610519 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1610518 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1607642 h3)). Qed.
Lemma lem1610520 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term184 y x) : False.
Proof. exact (EQ_MP (@lem1610519 y x h1 h2 h3 h4 h5) (@lem1607642 h3)). Qed.
Lemma lem1610521 (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term187 x) : False.
Proof. exact (ex_elim (@lem1607620 x h5) (fun y : real => fun h0 : term186 x y => @lem1610520 y x h1 h2 h3 h4 h0)). Qed.
Lemma lem1610522 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : False.
Proof. exact (ex_elim (@lem1607411 h5) (fun x : real => fun h0 : term188 x => @lem1610521 x h1 h2 h3 h4 h0)). Qed.
Lemma lem1610523 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1610522 h1 h2 h3 h4 h5) (fun h6 : False => @lem1607437 h4)). Qed.
Lemma lem1610524 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1610523 h1 h2 h3 h4 h5) (@lem1607437 h4)). Qed.
Lemma lem1610525 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1610524 h1 h2 h3 h4 h5) (fun h6 : False => @lem1607424 h3)). Qed.
Lemma lem1610526 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1610525 h1 h2 h3 h4 h5) (@lem1607424 h3)). Qed.
Lemma lem1610527 (h1 : term34) (h2 : term41) (h3 : term38) (h4 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1610526 h0 h1 h2 h3 h4). Qed.
Lemma lem1610528 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1610529 (h1 : term34) (h2 : term41) (h3 : term38) (h4 : term3) : term9.
Proof. exact (EQ_MP (@lem1610528) (@lem1610527 h1 h2 h3 h4)). Qed.
Lemma lem1610530 (h1 : term41) (h2 : term38) (h3 : term3) : term13.
Proof. exact (fun h0 : term34 => @lem1610529 h0 h1 h2 h3). Qed.
Lemma lem1610531 (h1 : term41) (h2 : term3) : term16.
Proof. exact (fun h0 : term38 => @lem1610530 h1 h0 h2). Qed.
Lemma lem1610532 (h1 : term3) : term19.
Proof. exact (fun h0 : term41 => @lem1610531 h0 h1). Qed.
Lemma lem1610533 : term21.
Proof. exact (fun h0 : term3 => @lem1610532 h0). Qed.
Lemma lem1610534 : term4.
Proof. exact (EQ_MP (@lem1606943) (@lem1610533)). Qed.
Lemma lem1610536 : term4.
Proof. exact (@lem1606667 (@lem1610534)). Qed.
Lemma lem1610537 (h1 : term3) : term18.
Proof. exact (@lem1610536 (@lem1606652 h1)). Qed.
Lemma lem1610538 (h1 : term3) : term15.
Proof. exact (@lem1610537 h1 (@lem1356740)). Qed.
Lemma lem1610539 (h1 : term3) : term12.
Proof. exact (@lem1610538 h1 (@lem1357243)). Qed.
Lemma lem1610540 (h1 : term3) : term8.
Proof. exact (@lem1610539 h1 (@lem1602515)). Qed.
Lemma lem1610541 (h1 : term3) : False.
Proof. exact (@lem1610540 h1 (@lem1602653)). Qed.
Lemma lem1610542 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1610541 h1) (fun h2 : False => @lem1606652 h1)). Qed.
Lemma lem1610543 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1610542 h1) (@lem1606652 h1)). Qed.
Lemma lem1610544 : term2.
Proof. exact (fun h0 : term3 => @lem1610543 h0). Qed.
Lemma lem1610545 : term1.
Proof. exact (EQ_MP (@lem1606651) (@lem1610544)). Qed.
