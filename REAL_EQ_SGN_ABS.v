Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_SGN_ABS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_SGN_ABS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1719711 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1719712 : term1 = term2.
Proof. exact (@lem1719711 term1). Qed.
Lemma lem1719713 : term2 = term1.
Proof. exact (SYM (@lem1719712)). Qed.
Lemma lem1719714 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1719717 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1719718 : term5.
Proof. exact (fun h0 : term4 => @lem1719717 h0). Qed.
Lemma lem1719719 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1719720 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1719721 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1719719 h2 (@lem1719720 h1)). Qed.
Lemma lem1719722 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1719721 h1 h0). Qed.
Lemma lem1719723 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1719724 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1719722 h1 (@lem1719723 h2)). Qed.
Lemma lem1719725 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1719724 h0 h1). Qed.
Lemma lem1719726 : term7.
Proof. exact (fun h0 : term5 => @lem1719725 h0). Qed.
Lemma lem1719729 : term5.
Proof. exact (@lem1719726 (@lem1719718)). Qed.
Lemma lem1719743 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1719744 : term8 = term9.
Proof. exact (@lem1719743 term10). Qed.
Lemma lem1719749 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1719756 : term4 = term12.
Proof. exact (MK_COMB (@lem1719749) (@lem1719744)). Qed.
Lemma lem1719757 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1719758 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1719757 x)). Qed.
Lemma lem1719759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1719760 : term10 = term10.
Proof. exact (MK_COMB (@lem1719759) (@lem1719758)). Qed.
Lemma lem1719761 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1719762 : term9 = term9.
Proof. exact (MK_COMB (@lem1719761) (@lem1719760)). Qed.
Lemma lem1719771 (x : real) (y : real) : ((x = y) = (term15 x y)) = ((x = y) = (term15 x y)).
Proof. exact (eq_refl ((x = y) = (term15 x y))). Qed.
Lemma lem1719772 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1719771 x y)). Qed.
Lemma lem1719773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1719774 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1719773) (@lem1719772 x)). Qed.
Lemma lem1719775 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1719774 x)). Qed.
Lemma lem1719776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1719777 : term1 = term1.
Proof. exact (MK_COMB (@lem1719776) (@lem1719775)). Qed.
Lemma lem1719778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1719779 : term3 = term3.
Proof. exact (MK_COMB (@lem1719778) (@lem1719777)). Qed.
Lemma lem1719780 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1719781 : term11 = term11.
Proof. exact (MK_COMB (@lem1719780) (@lem1719779)). Qed.
Lemma lem1719782 : term12 = term12.
Proof. exact (MK_COMB (@lem1719781) (@lem1719762)). Qed.
Lemma lem1719807 : term4 = term12.
Proof. exact (TRANS (@lem1719756) (@lem1719782)). Qed.
Lemma lem1719808 : term12 = term4.
Proof. exact (SYM (@lem1719807)). Qed.
Lemma lem1719809 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1719810 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1719821 (x : real) (y : real) : (term19 x y) = (term20 x y).
Proof. exact (@lem17045 ((real_sgn x) = (real_sgn y)) ((real_abs x) = (real_abs y))). Qed.
Lemma lem1719827 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1719829 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1719830 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1719829 x y) (@lem1719821 x y)). Qed.
Lemma lem1719831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719832 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1719831) (@lem1719830 x y)). Qed.
Lemma lem1719833 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1719832 x y) (@lem1719827 x y)). Qed.
Lemma lem1719834 (x : real) (y : real) : (term29 x y) = (term27 x y).
Proof. exact (@lem17646 (x = y) (term15 x y)). Qed.
Lemma lem1719835 (x : real) (y : real) : (term29 x y) = (term28 x y).
Proof. exact (TRANS (@lem1719834 x y) (@lem1719833 x y)). Qed.
Lemma lem1719836 (P : real -> Prop) : (term30 P) = (term31 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1719837 (x : real) : (term32 x) = (term33 x).
Proof. exact (@lem1719836 (term16 x)). Qed.
Lemma lem1719838 (x : real) (y : real) : (term34 x y) = ((x = y) = (term15 x y)).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1719839 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1719840 (x : real) (y : real) : (term35 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1719839) (@lem1719838 x y)). Qed.
Lemma lem1719841 (x : real) (y : real) : (term35 x y) = (term28 x y).
Proof. exact (TRANS (@lem1719840 x y) (@lem1719835 x y)). Qed.
Lemma lem1719842 (x : real) : (term36 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1719841 x y)). Qed.
Lemma lem1719843 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719844 (x : real) : (term33 x) = (term38 x).
Proof. exact (MK_COMB (@lem1719843) (@lem1719842 x)). Qed.
Lemma lem1719845 (x : real) : (term32 x) = (term38 x).
Proof. exact (TRANS (@lem1719837 x) (@lem1719844 x)). Qed.
Lemma lem1719846 (P : real -> Prop) : (term30 P) = (term31 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1719847 : term3 = term39.
Proof. exact (@lem1719846 term18). Qed.
Lemma lem1719848 (x : real) : (term40 x) = (term17 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1719849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1719850 (x : real) : (term41 x) = (term32 x).
Proof. exact (MK_COMB (@lem1719849) (@lem1719848 x)). Qed.
Lemma lem1719851 (x : real) : (term41 x) = (term38 x).
Proof. exact (TRANS (@lem1719850 x) (@lem1719845 x)). Qed.
Lemma lem1719852 : term42 = term43.
Proof. exact (fun_ext (fun x : real => @lem1719851 x)). Qed.
Lemma lem1719853 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719854 : term39 = term44.
Proof. exact (MK_COMB (@lem1719853) (@lem1719852)). Qed.
Lemma lem1719855 : term3 = term44.
Proof. exact (TRANS (@lem1719847) (@lem1719854)). Qed.
Lemma lem1719861 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1719862 (P : real -> Prop) (Q : real -> Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem1719861 real P Q). Qed.
Lemma lem1719863 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1719862 (term51 x) (term52 x)). Qed.
Lemma lem1719864 (x : real) (y : real) : (term53 x y) = (term24 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1719865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719866 (x : real) (y : real) : (term54 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1719865) (@lem1719864 x y)). Qed.
Lemma lem1719867 (x : real) (y : real) : (term55 x y) = (term21 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1719868 (x : real) (y : real) : (term56 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1719866 x y) (@lem1719867 x y)). Qed.
Lemma lem1719869 (x : real) : (term57 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1719868 x y)). Qed.
Lemma lem1719870 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719871 (x : real) : (term49 x) = (term38 x).
Proof. exact (MK_COMB (@lem1719870) (@lem1719869 x)). Qed.
Lemma lem1719872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1719873 (x : real) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem1719872) (@lem1719871 x)). Qed.
Lemma lem1719874 (x : real) (y : real) : (term53 x y) = (term24 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1719875 (x : real) : (term60 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1719874 x y)). Qed.
Lemma lem1719876 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719877 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1719876) (@lem1719875 x)). Qed.
Lemma lem1719878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719879 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1719878) (@lem1719877 x)). Qed.
Lemma lem1719880 (x : real) (y : real) : (term55 x y) = (term21 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1719881 (x : real) : (term65 x) = (term52 x).
Proof. exact (fun_ext (fun y : real => @lem1719880 x y)). Qed.
Lemma lem1719882 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719883 (x : real) : (term66 x) = (term67 x).
Proof. exact (MK_COMB (@lem1719882) (@lem1719881 x)). Qed.
Lemma lem1719884 (x : real) : (term50 x) = (term68 x).
Proof. exact (MK_COMB (@lem1719879 x) (@lem1719883 x)). Qed.
Lemma lem1719885 (x : real) : ((term49 x) = (term50 x)) = ((term38 x) = (term68 x)).
Proof. exact (MK_COMB (@lem1719873 x) (@lem1719884 x)). Qed.
Lemma lem1719886 (x : real) : (term38 x) = (term68 x).
Proof. exact (EQ_MP (@lem1719885 x) (@lem1719863 x)). Qed.
Lemma lem1719983 : term43 = term69.
Proof. exact (fun_ext (fun x : real => @lem1719886 x)). Qed.
Lemma lem1719984 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719985 : term44 = term70.
Proof. exact (MK_COMB (@lem1719984) (@lem1719983)). Qed.
Lemma lem1719987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1719988 (P : real -> Prop) (Q : real -> Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem1719987 real P Q). Qed.
Lemma lem1719989 : term71 = term72.
Proof. exact (@lem1719988 term73 term74). Qed.
Lemma lem1719990 (x : real) : (term75 x) = (term62 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1719991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719992 (x : real) : (term76 x) = (term64 x).
Proof. exact (MK_COMB (@lem1719991) (@lem1719990 x)). Qed.
Lemma lem1719993 (x : real) : (term77 x) = (term67 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1719994 (x : real) : (term78 x) = (term68 x).
Proof. exact (MK_COMB (@lem1719992 x) (@lem1719993 x)). Qed.
Lemma lem1719995 : term79 = term69.
Proof. exact (fun_ext (fun x : real => @lem1719994 x)). Qed.
Lemma lem1719996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1719997 : term71 = term70.
Proof. exact (MK_COMB (@lem1719996) (@lem1719995)). Qed.
Lemma lem1719998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1719999 : term80 = term81.
Proof. exact (MK_COMB (@lem1719998) (@lem1719997)). Qed.
Lemma lem1720000 (x : real) : (term75 x) = (term62 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1720001 : term82 = term73.
Proof. exact (fun_ext (fun x : real => @lem1720000 x)). Qed.
Lemma lem1720002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720003 : term83 = term84.
Proof. exact (MK_COMB (@lem1720002) (@lem1720001)). Qed.
Lemma lem1720004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1720005 : term85 = term86.
Proof. exact (MK_COMB (@lem1720004) (@lem1720003)). Qed.
Lemma lem1720006 (x : real) : (term77 x) = (term67 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1720007 : term87 = term74.
Proof. exact (fun_ext (fun x : real => @lem1720006 x)). Qed.
Lemma lem1720008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720009 : term88 = term89.
Proof. exact (MK_COMB (@lem1720008) (@lem1720007)). Qed.
Lemma lem1720010 : term72 = term90.
Proof. exact (MK_COMB (@lem1720005) (@lem1720009)). Qed.
Lemma lem1720011 : (term71 = term72) = (term70 = term90).
Proof. exact (MK_COMB (@lem1719999) (@lem1720010)). Qed.
Lemma lem1720012 : term70 = term90.
Proof. exact (EQ_MP (@lem1720011) (@lem1719989)). Qed.
Lemma lem1720117 : term44 = term90.
Proof. exact (TRANS (@lem1719985) (@lem1720012)). Qed.
Lemma lem1720119 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term45 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1720120 (P : real -> Prop) (Q : real -> Prop) : (term48 P Q) = (term47 P Q).
Proof. exact (@lem1720119 real P Q). Qed.
Lemma lem1720121 : term72 = term71.
Proof. exact (@lem1720120 term73 term74). Qed.
Lemma lem1720122 (x : real) : (term75 x) = (term62 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1720123 : term82 = term73.
Proof. exact (fun_ext (fun x : real => @lem1720122 x)). Qed.
Lemma lem1720124 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720125 : term83 = term84.
Proof. exact (MK_COMB (@lem1720124) (@lem1720123)). Qed.
Lemma lem1720126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1720127 : term85 = term86.
Proof. exact (MK_COMB (@lem1720126) (@lem1720125)). Qed.
Lemma lem1720128 (x : real) : (term77 x) = (term67 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1720129 : term87 = term74.
Proof. exact (fun_ext (fun x : real => @lem1720128 x)). Qed.
Lemma lem1720130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720131 : term88 = term89.
Proof. exact (MK_COMB (@lem1720130) (@lem1720129)). Qed.
Lemma lem1720132 : term72 = term90.
Proof. exact (MK_COMB (@lem1720127) (@lem1720131)). Qed.
Lemma lem1720133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1720134 : term91 = term92.
Proof. exact (MK_COMB (@lem1720133) (@lem1720132)). Qed.
Lemma lem1720135 (x : real) : (term75 x) = (term62 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1720136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1720137 (x : real) : (term76 x) = (term64 x).
Proof. exact (MK_COMB (@lem1720136) (@lem1720135 x)). Qed.
Lemma lem1720138 (x : real) : (term77 x) = (term67 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1720139 (x : real) : (term78 x) = (term68 x).
Proof. exact (MK_COMB (@lem1720137 x) (@lem1720138 x)). Qed.
Lemma lem1720140 : term79 = term69.
Proof. exact (fun_ext (fun x : real => @lem1720139 x)). Qed.
Lemma lem1720141 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720142 : term71 = term70.
Proof. exact (MK_COMB (@lem1720141) (@lem1720140)). Qed.
Lemma lem1720143 : (term72 = term71) = (term90 = term70).
Proof. exact (MK_COMB (@lem1720134) (@lem1720142)). Qed.
Lemma lem1720144 : term90 = term70.
Proof. exact (EQ_MP (@lem1720143) (@lem1720121)). Qed.
Lemma lem1720146 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term45 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1720147 (P : real -> Prop) (Q : real -> Prop) : (term48 P Q) = (term47 P Q).
Proof. exact (@lem1720146 real P Q). Qed.
Lemma lem1720148 (x : real) : (term50 x) = (term49 x).
Proof. exact (@lem1720147 (term51 x) (term52 x)). Qed.
Lemma lem1720149 (x : real) (y : real) : (term53 x y) = (term24 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1720150 (x : real) : (term60 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1720149 x y)). Qed.
Lemma lem1720151 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720152 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1720151) (@lem1720150 x)). Qed.
Lemma lem1720153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1720154 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1720153) (@lem1720152 x)). Qed.
Lemma lem1720155 (x : real) (y : real) : (term55 x y) = (term21 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1720156 (x : real) : (term65 x) = (term52 x).
Proof. exact (fun_ext (fun y : real => @lem1720155 x y)). Qed.
Lemma lem1720157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720158 (x : real) : (term66 x) = (term67 x).
Proof. exact (MK_COMB (@lem1720157) (@lem1720156 x)). Qed.
Lemma lem1720159 (x : real) : (term50 x) = (term68 x).
Proof. exact (MK_COMB (@lem1720154 x) (@lem1720158 x)). Qed.
Lemma lem1720160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1720161 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1720160) (@lem1720159 x)). Qed.
Lemma lem1720162 (x : real) (y : real) : (term53 x y) = (term24 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1720163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1720164 (x : real) (y : real) : (term54 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1720163) (@lem1720162 x y)). Qed.
Lemma lem1720165 (x : real) (y : real) : (term55 x y) = (term21 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1720166 (x : real) (y : real) : (term56 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1720164 x y) (@lem1720165 x y)). Qed.
Lemma lem1720167 (x : real) : (term57 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1720166 x y)). Qed.
Lemma lem1720168 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720169 (x : real) : (term49 x) = (term38 x).
Proof. exact (MK_COMB (@lem1720168) (@lem1720167 x)). Qed.
Lemma lem1720170 (x : real) : ((term50 x) = (term49 x)) = ((term68 x) = (term38 x)).
Proof. exact (MK_COMB (@lem1720161 x) (@lem1720169 x)). Qed.
Lemma lem1720171 (x : real) : (term68 x) = (term38 x).
Proof. exact (EQ_MP (@lem1720170 x) (@lem1720148 x)). Qed.
Lemma lem1720172 : term69 = term43.
Proof. exact (fun_ext (fun x : real => @lem1720171 x)). Qed.
Lemma lem1720173 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720174 : term70 = term44.
Proof. exact (MK_COMB (@lem1720173) (@lem1720172)). Qed.
Lemma lem1720175 : term90 = term44.
Proof. exact (TRANS (@lem1720144) (@lem1720174)). Qed.
Lemma lem1720176 : term44 = term44.
Proof. exact (TRANS (@lem1720117) (@lem1720175)). Qed.
Lemma lem1720177 : term3 = term44.
Proof. exact (TRANS (@lem1719855) (@lem1720176)). Qed.
Lemma lem1720178 (h1 : term3) : term44.
Proof. exact (EQ_MP (@lem1720177) (@lem1719809 h1)). Qed.
Lemma lem1720179 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1720180 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1720179 x)). Qed.
Lemma lem1720181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1720190 : term10 = term10.
Proof. exact (MK_COMB (@lem1720181) (@lem1720180)). Qed.
Lemma lem1720191 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1720190) (@lem1719810 h1)). Qed.
Lemma lem1720192 (x : real) (h1 : term38 x) : term38 x.
Proof. exact (h1). Qed.
Lemma lem1720206 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1720207 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1720206 x)). Qed.
Lemma lem1720208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1720209 : term10 = term10.
Proof. exact (MK_COMB (@lem1720208) (@lem1720207)). Qed.
Lemma lem1720210 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1720209) (@lem1720191 h1)). Qed.
Lemma lem1720278 (x : real) (y : real) (h1 : term28 x y) : term28 x y.
Proof. exact (h1). Qed.
Lemma lem1720279 (x : real) (y : real) (h1 : term24 x y) : term24 x y.
Proof. exact (h1). Qed.
Lemma lem1720280 (x : real) (y : real) (h1 : term21 x y) : term21 x y.
Proof. exact (h1). Qed.
Lemma lem1720281 (x : real) (y : real) (h1 : term24 x y) : term20 x y.
Proof. exact (proj2 (@lem1720279 x y h1)). Qed.
Lemma lem1720285 (x : real) (y : real) (h1 : term21 x y) : term15 x y.
Proof. exact (proj2 (@lem1720280 x y h1)). Qed.
Lemma lem1720303 (x : real) (y : real) (h1 : term95 x y) : term95 x y.
Proof. exact (h1). Qed.
Lemma lem1720318 (x : real) (y : real) (h1 : term96 x y) : term96 x y.
Proof. exact (h1). Qed.
Lemma lem1720320 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1720321 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1720320 x)). Qed.
Lemma lem1720322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1720324 : term10 = term10.
Proof. exact (MK_COMB (@lem1720322) (@lem1720321)). Qed.
Lemma lem1720325 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1720324) (@lem1720210 h1)). Qed.
Lemma lem1720344 (_26492 : real) (h1 : term10) : term97 _26492.
Proof. exact (@lem1720325 h1 _26492). Qed.
Lemma lem1720345 (_26492 : real) : (term97 _26492) = ((term13 _26492) = _26492).
Proof. exact (eq_refl (term97 _26492)). Qed.
Lemma lem1720350 (x : real) (y : real) (h1 : term24 x y) : x = y.
Proof. exact (proj1 (@lem1720279 x y h1)). Qed.
Lemma lem1720352 (x : real) (y : real) (h1 : term95 x y) : term95 x y.
Proof. exact (h1). Qed.
Lemma lem1720356 (x : real) (y : real) (h1 : term24 x y) : x = y.
Proof. exact (proj1 (@lem1720279 x y h1)). Qed.
Lemma lem1720358 (x : real) (y : real) (h1 : term96 x y) : term96 x y.
Proof. exact (h1). Qed.
Lemma lem1720362 (x : real) (y : real) (h1 : term21 x y) : term98 x y.
Proof. exact (proj1 (@lem1720280 x y h1)). Qed.
Lemma lem1720395 (y : real) : (term99 y) = (term99 y).
Proof. exact (eq_refl (term99 y)). Qed.
Lemma lem1720396 (x : real) (y : real) (h1 : term24 x y) : (term100 y x) = (term101 y).
Proof. exact (MK_COMB (@lem1720395 y) (@lem1720350 x y h1)). Qed.
Lemma lem1720397 (y : real) : (term101 y) = (term102 y).
Proof. exact (eq_refl (term101 y)). Qed.
Lemma lem1720398 (y : real) (x : real) : (term103 y x) = (term103 y x).
Proof. exact (eq_refl (term103 y x)). Qed.
Lemma lem1720399 (x : real) (y : real) : ((term100 y x) = (term101 y)) = ((term100 y x) = (term102 y)).
Proof. exact (MK_COMB (@lem1720398 y x) (@lem1720397 y)). Qed.
Lemma lem1720400 (x : real) (y : real) : (term100 y x) = (term95 x y).
Proof. exact (eq_refl (term100 y x)). Qed.
Lemma lem1720401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1720402 (x : real) (y : real) : (term103 y x) = (term104 x y).
Proof. exact (MK_COMB (@lem1720401) (@lem1720400 x y)). Qed.
Lemma lem1720403 (y : real) : (term102 y) = (term102 y).
Proof. exact (eq_refl (term102 y)). Qed.
Lemma lem1720404 (x : real) (y : real) : ((term100 y x) = (term102 y)) = ((term95 x y) = (term102 y)).
Proof. exact (MK_COMB (@lem1720402 x y) (@lem1720403 y)). Qed.
Lemma lem1720405 (x : real) (y : real) : ((term100 y x) = (term101 y)) = ((term95 x y) = (term102 y)).
Proof. exact (TRANS (@lem1720399 x y) (@lem1720404 x y)). Qed.
Lemma lem1720406 (x : real) (y : real) (h1 : term24 x y) : (term95 x y) = (term102 y).
Proof. exact (EQ_MP (@lem1720405 x y) (@lem1720396 x y h1)). Qed.
Lemma lem1720407 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : term102 y.
Proof. exact (EQ_MP (@lem1720406 x y h2) (@lem1720352 x y h1)). Qed.
Lemma lem1720436 (y : real) : (term105 y) = (term105 y).
Proof. exact (eq_refl (term105 y)). Qed.
Lemma lem1720437 (x : real) (y : real) (h1 : term24 x y) : (term106 y x) = (term107 y).
Proof. exact (MK_COMB (@lem1720436 y) (@lem1720356 x y h1)). Qed.
Lemma lem1720438 (y : real) : (term107 y) = (term108 y).
Proof. exact (eq_refl (term107 y)). Qed.
Lemma lem1720439 (y : real) (x : real) : (term109 y x) = (term109 y x).
Proof. exact (eq_refl (term109 y x)). Qed.
Lemma lem1720440 (x : real) (y : real) : ((term106 y x) = (term107 y)) = ((term106 y x) = (term108 y)).
Proof. exact (MK_COMB (@lem1720439 y x) (@lem1720438 y)). Qed.
Lemma lem1720441 (x : real) (y : real) : (term106 y x) = (term96 x y).
Proof. exact (eq_refl (term106 y x)). Qed.
Lemma lem1720442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1720443 (x : real) (y : real) : (term109 y x) = (term110 x y).
Proof. exact (MK_COMB (@lem1720442) (@lem1720441 x y)). Qed.
Lemma lem1720444 (y : real) : (term108 y) = (term108 y).
Proof. exact (eq_refl (term108 y)). Qed.
Lemma lem1720445 (x : real) (y : real) : ((term106 y x) = (term108 y)) = ((term96 x y) = (term108 y)).
Proof. exact (MK_COMB (@lem1720443 x y) (@lem1720444 y)). Qed.
Lemma lem1720446 (x : real) (y : real) : ((term106 y x) = (term107 y)) = ((term96 x y) = (term108 y)).
Proof. exact (TRANS (@lem1720440 x y) (@lem1720445 x y)). Qed.
Lemma lem1720447 (x : real) (y : real) (h1 : term24 x y) : (term96 x y) = (term108 y).
Proof. exact (EQ_MP (@lem1720446 x y) (@lem1720437 x y h1)). Qed.
Lemma lem1720448 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : term108 y.
Proof. exact (EQ_MP (@lem1720447 x y h2) (@lem1720358 x y h1)). Qed.
Lemma lem1720483 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1720484 (y : real) : (real_sgn y) = (real_sgn y).
Proof. exact (@lem1720483 (real_sgn y)). Qed.
Lemma lem1720485 (y : real) : term111 y.
Proof. exact (fun h0 : term102 y => @lem1720484 y). Qed.
Lemma lem1720487 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720488 (y : real) : (term111 y) = ((real_sgn y) = (real_sgn y)).
Proof. exact (@lem1720487 ((real_sgn y) = (real_sgn y))). Qed.
Lemma lem1720489 (y : real) : (real_sgn y) = (real_sgn y).
Proof. exact (EQ_MP (@lem1720488 y) (@lem1720485 y)). Qed.
Lemma lem1720492 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1720494 (y : real) : (term102 y) = (term113 y).
Proof. exact (@lem1720492 ((real_sgn y) = (real_sgn y))). Qed.
Lemma lem1720497 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : term113 y.
Proof. exact (EQ_MP (@lem1720494 y) (@lem1720407 x y h1 h2)). Qed.
Lemma lem1720500 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : False.
Proof. exact (@lem1720497 x y h1 h2 (@lem1720489 y)). Qed.
Lemma lem1720501 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : term114.
Proof. exact (fun h0 : ~ False => @lem1720500 x y h1 h2). Qed.
Lemma lem1720503 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720504 : term114 = False.
Proof. exact (@lem1720503 False). Qed.
Lemma lem1720540 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1720541 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (@lem1720540 (real_abs y)). Qed.
Lemma lem1720542 (y : real) : term115 y.
Proof. exact (fun h0 : term108 y => @lem1720541 y). Qed.
Lemma lem1720544 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720545 (y : real) : (term115 y) = ((real_abs y) = (real_abs y)).
Proof. exact (@lem1720544 ((real_abs y) = (real_abs y))). Qed.
Lemma lem1720546 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (EQ_MP (@lem1720545 y) (@lem1720542 y)). Qed.
Lemma lem1720549 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1720551 (y : real) : (term108 y) = (term116 y).
Proof. exact (@lem1720549 ((real_abs y) = (real_abs y))). Qed.
Lemma lem1720554 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : term116 y.
Proof. exact (EQ_MP (@lem1720551 y) (@lem1720448 x y h1 h2)). Qed.
Lemma lem1720557 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : False.
Proof. exact (@lem1720554 x y h1 h2 (@lem1720546 y)). Qed.
Lemma lem1720558 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : term114.
Proof. exact (fun h0 : ~ False => @lem1720557 x y h1 h2). Qed.
Lemma lem1720560 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720561 : term114 = False.
Proof. exact (@lem1720560 False). Qed.
Lemma lem1720579 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1720580 (_26525 : real) (_26527 : real) (h1 : _26525 = _26527) : _26525 = _26527.
Proof. exact (h1). Qed.
Lemma lem1720581 (_26526 : real) (_26528 : real) (h1 : _26526 = _26528) : _26526 = _26528.
Proof. exact (h1). Qed.
Lemma lem1720582 (_26525 : real) (_26527 : real) (h1 : _26525 = _26527) : (real_mul _26525) = (real_mul _26527).
Proof. exact (MK_COMB (@lem1720579) (@lem1720580 _26525 _26527 h1)). Qed.
Lemma lem1720583 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) (h1 : _26525 = _26527) (h2 : _26526 = _26528) : (real_mul _26525 _26526) = (real_mul _26527 _26528).
Proof. exact (MK_COMB (@lem1720582 _26525 _26527 h1) (@lem1720581 _26526 _26528 h2)). Qed.
Lemma lem1720584 (_26526 : real) (_26528 : real) (_26525 : real) (_26527 : real) (h1 : _26525 = _26527) : term117 _26525 _26526 _26527 _26528.
Proof. exact (fun h0 : _26526 = _26528 => @lem1720583 _26525 _26527 _26526 _26528 h1 h0). Qed.
Lemma lem1720586 (a : Prop) (b : Prop) : (a -> b) = (term118 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1720587 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : (term117 _26525 _26526 _26527 _26528) = (term119 _26525 _26526 _26527 _26528).
Proof. exact (@lem1720586 (_26526 = _26528) ((real_mul _26525 _26526) = (real_mul _26527 _26528))). Qed.
Lemma lem1720588 (_26526 : real) (_26528 : real) (_26525 : real) (_26527 : real) (h1 : _26525 = _26527) : term119 _26525 _26526 _26527 _26528.
Proof. exact (EQ_MP (@lem1720587 _26525 _26526 _26527 _26528) (@lem1720584 _26526 _26528 _26525 _26527 h1)). Qed.
Lemma lem1720589 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : term120 _26525 _26526 _26527 _26528.
Proof. exact (fun h0 : _26525 = _26527 => @lem1720588 _26526 _26528 _26525 _26527 h0). Qed.
Lemma lem1720591 (a : Prop) (b : Prop) : (a -> b) = (term118 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1720592 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : (term120 _26525 _26526 _26527 _26528) = (term121 _26525 _26526 _26527 _26528).
Proof. exact (@lem1720591 (_26525 = _26527) (term119 _26525 _26526 _26527 _26528)). Qed.
Lemma lem1720593 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : term121 _26525 _26526 _26527 _26528.
Proof. exact (EQ_MP (@lem1720592 _26525 _26526 _26527 _26528) (@lem1720589 _26525 _26526 _26527 _26528)). Qed.
Lemma lem1720595 (x : real) (y : real) (z : real) : term122 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1720597 (x : real) (y : real) (h1 : term21 x y) : (real_sgn x) = (real_sgn y).
Proof. exact (proj1 (@lem1720285 x y h1)). Qed.
Lemma lem1720598 (x : real) (y : real) (h1 : term21 x y) : term123 x y.
Proof. exact (fun h0 : term95 x y => @lem1720597 x y h1). Qed.
Lemma lem1720600 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720601 (x : real) (y : real) : (term123 x y) = ((real_sgn x) = (real_sgn y)).
Proof. exact (@lem1720600 ((real_sgn x) = (real_sgn y))). Qed.
Lemma lem1720602 (x : real) (y : real) (h1 : term21 x y) : (real_sgn x) = (real_sgn y).
Proof. exact (EQ_MP (@lem1720601 x y) (@lem1720598 x y h1)). Qed.
Lemma lem1720604 (x : real) (y : real) (h1 : term21 x y) : (real_abs x) = (real_abs y).
Proof. exact (proj2 (@lem1720285 x y h1)). Qed.
Lemma lem1720605 (x : real) (y : real) (h1 : term21 x y) : term124 x y.
Proof. exact (fun h0 : term96 x y => @lem1720604 x y h1). Qed.
Lemma lem1720607 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720608 (x : real) (y : real) : (term124 x y) = ((real_abs x) = (real_abs y)).
Proof. exact (@lem1720607 ((real_abs x) = (real_abs y))). Qed.
Lemma lem1720609 (x : real) (y : real) (h1 : term21 x y) : (real_abs x) = (real_abs y).
Proof. exact (EQ_MP (@lem1720608 x y) (@lem1720605 x y h1)). Qed.
Lemma lem1720627 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1720628 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term119 _26525 _26526 _26527 _26528) = (term125 _26525 _26527 _26526 _26528).
Proof. exact (@lem1720627 ((real_mul _26525 _26526) = (real_mul _26527 _26528)) (term98 _26526 _26528)). Qed.
Lemma lem1720638 (_26525 : real) (_26527 : real) : (term126 _26525 _26527) = (term126 _26525 _26527).
Proof. exact (eq_refl (term126 _26525 _26527)). Qed.
Lemma lem1720639 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term121 _26525 _26526 _26527 _26528) = (term127 _26525 _26527 _26526 _26528).
Proof. exact (MK_COMB (@lem1720638 _26525 _26527) (@lem1720628 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720643 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1720644 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term127 _26525 _26527 _26526 _26528) = (term129 _26525 _26527 _26526 _26528).
Proof. exact (@lem1720643 ((real_mul _26525 _26526) = (real_mul _26527 _26528)) (term98 _26525 _26527) (term98 _26526 _26528)). Qed.
Lemma lem1720666 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term121 _26525 _26526 _26527 _26528) = (term129 _26525 _26527 _26526 _26528).
Proof. exact (TRANS (@lem1720639 _26525 _26527 _26526 _26528) (@lem1720644 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1720668 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term130 _26525 _26526 _26527 _26528) = (term131 _26525 _26527 _26526 _26528).
Proof. exact (MK_COMB (@lem1720667) (@lem1720666 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720690 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term129 _26525 _26527 _26526 _26528) = (term129 _26525 _26527 _26526 _26528).
Proof. exact (eq_refl (term129 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720691 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : ((term121 _26525 _26526 _26527 _26528) = (term129 _26525 _26527 _26526 _26528)) = ((term129 _26525 _26527 _26526 _26528) = (term129 _26525 _26527 _26526 _26528)).
Proof. exact (MK_COMB (@lem1720668 _26525 _26527 _26526 _26528) (@lem1720690 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720693 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1720694 (x : Prop) : (x = x) = True.
Proof. exact (@lem1720693 Prop x). Qed.
Lemma lem1720695 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : ((term129 _26525 _26527 _26526 _26528) = (term129 _26525 _26527 _26526 _26528)) = True.
Proof. exact (@lem1720694 (term129 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720696 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : ((term121 _26525 _26526 _26527 _26528) = (term129 _26525 _26527 _26526 _26528)) = True.
Proof. exact (TRANS (@lem1720691 _26525 _26527 _26526 _26528) (@lem1720695 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720697 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : True = ((term121 _26525 _26526 _26527 _26528) = (term129 _26525 _26527 _26526 _26528)).
Proof. exact (SYM (@lem1720696 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720698 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term121 _26525 _26526 _26527 _26528) = (term129 _26525 _26527 _26526 _26528).
Proof. exact (EQ_MP (@lem1720697 _26525 _26527 _26526 _26528) (@lem0)). Qed.
Lemma lem1720699 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : term129 _26525 _26527 _26526 _26528.
Proof. exact (EQ_MP (@lem1720698 _26525 _26527 _26526 _26528) (@lem1720593 _26525 _26526 _26527 _26528)). Qed.
Lemma lem1720701 (b : Prop) (a : Prop) : (a \/ b) = (term132 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1720702 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : (term129 _26525 _26527 _26526 _26528) = (term133 _26525 _26526 _26527 _26528).
Proof. exact (@lem1720701 (term134 _26525 _26527 _26526 _26528) ((real_mul _26525 _26526) = (real_mul _26527 _26528))). Qed.
Lemma lem1720704 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1720705 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term137 _26525 _26527 _26526 _26528) = (term138 _26525 _26527 _26526 _26528).
Proof. exact (@lem1720704 (term98 _26525 _26527) (term98 _26526 _26528)). Qed.
Lemma lem1720707 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1720708 (_26525 : real) (_26527 : real) : (term140 _26525 _26527) = (_26525 = _26527).
Proof. exact (@lem1720707 (_26525 = _26527)). Qed.
Lemma lem1720709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1720710 (_26525 : real) (_26527 : real) : (term141 _26525 _26527) = (term22 _26525 _26527).
Proof. exact (MK_COMB (@lem1720709) (@lem1720708 _26525 _26527)). Qed.
Lemma lem1720712 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1720713 (_26526 : real) (_26528 : real) : (term140 _26526 _26528) = (_26526 = _26528).
Proof. exact (@lem1720712 (_26526 = _26528)). Qed.
Lemma lem1720714 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term138 _26525 _26527 _26526 _26528) = (term142 _26525 _26527 _26526 _26528).
Proof. exact (MK_COMB (@lem1720710 _26525 _26527) (@lem1720713 _26526 _26528)). Qed.
Lemma lem1720715 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term137 _26525 _26527 _26526 _26528) = (term142 _26525 _26527 _26526 _26528).
Proof. exact (TRANS (@lem1720705 _26525 _26527 _26526 _26528) (@lem1720714 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720716 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1720717 (_26525 : real) (_26527 : real) (_26526 : real) (_26528 : real) : (term143 _26525 _26527 _26526 _26528) = (term144 _26525 _26527 _26526 _26528).
Proof. exact (MK_COMB (@lem1720716) (@lem1720715 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720718 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : ((real_mul _26525 _26526) = (real_mul _26527 _26528)) = ((real_mul _26525 _26526) = (real_mul _26527 _26528)).
Proof. exact (eq_refl ((real_mul _26525 _26526) = (real_mul _26527 _26528))). Qed.
Lemma lem1720719 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : (term133 _26525 _26526 _26527 _26528) = (term145 _26525 _26526 _26527 _26528).
Proof. exact (MK_COMB (@lem1720717 _26525 _26527 _26526 _26528) (@lem1720718 _26525 _26526 _26527 _26528)). Qed.
Lemma lem1720720 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : (term129 _26525 _26527 _26526 _26528) = (term145 _26525 _26526 _26527 _26528).
Proof. exact (TRANS (@lem1720702 _26525 _26526 _26527 _26528) (@lem1720719 _26525 _26526 _26527 _26528)). Qed.
Lemma lem1720722 (x : real) (y : real) (h1 : term21 x y) : term15 x y.
Proof. exact (conj (@lem1720602 x y h1) (@lem1720609 x y h1)). Qed.
Lemma lem1720724 (_26525 : real) (_26526 : real) (_26527 : real) (_26528 : real) : term145 _26525 _26526 _26527 _26528.
Proof. exact (EQ_MP (@lem1720720 _26525 _26526 _26527 _26528) (@lem1720699 _26525 _26527 _26526 _26528)). Qed.
Lemma lem1720725 (x : real) (y : real) : term146 x y.
Proof. exact (@lem1720724 (real_sgn x) (real_abs x) (real_sgn y) (real_abs y)). Qed.
Lemma lem1720728 (x : real) (y : real) (h1 : term21 x y) : (term13 x) = (term13 y).
Proof. exact (@lem1720725 x y (@lem1720722 x y h1)). Qed.
Lemma lem1720729 (x : real) (y : real) (h1 : term21 x y) : term147 x y.
Proof. exact (fun h0 : term148 x y => @lem1720728 x y h1). Qed.
Lemma lem1720731 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720732 (x : real) (y : real) : (term147 x y) = ((term13 x) = (term13 y)).
Proof. exact (@lem1720731 ((term13 x) = (term13 y))). Qed.
Lemma lem1720733 (x : real) (y : real) (h1 : term21 x y) : (term13 x) = (term13 y).
Proof. exact (EQ_MP (@lem1720732 x y) (@lem1720729 x y h1)). Qed.
Lemma lem1720735 (_26492 : real) (h1 : term10) : (term13 _26492) = _26492.
Proof. exact (EQ_MP (@lem1720345 _26492) (@lem1720344 _26492 h1)). Qed.
Lemma lem1720736 (x : real) (h1 : term10) : (term13 x) = x.
Proof. exact (@lem1720735 x h1). Qed.
Lemma lem1720737 (x : real) (h1 : term10) : term149 x.
Proof. exact (fun h0 : term150 x => @lem1720736 x h1). Qed.
Lemma lem1720739 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720740 (x : real) : (term149 x) = ((term13 x) = x).
Proof. exact (@lem1720739 ((term13 x) = x)). Qed.
Lemma lem1720741 (x : real) (h1 : term10) : (term13 x) = x.
Proof. exact (EQ_MP (@lem1720740 x) (@lem1720737 x h1)). Qed.
Lemma lem1720759 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1720760 (y : real) (x : real) (z : real) : (term151 x y z) = (term152 y x z).
Proof. exact (@lem1720759 (y = z) (term98 x z)). Qed.
Lemma lem1720770 (x : real) (y : real) : (term126 x y) = (term126 x y).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem1720771 (y : real) (x : real) (z : real) : (term122 x y z) = (term153 y x z).
Proof. exact (MK_COMB (@lem1720770 x y) (@lem1720760 y x z)). Qed.
Lemma lem1720775 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1720776 (y : real) (x : real) (z : real) : (term153 y x z) = (term154 y x z).
Proof. exact (@lem1720775 (y = z) (term98 x y) (term98 x z)). Qed.
Lemma lem1720798 (y : real) (x : real) (z : real) : (term122 x y z) = (term154 y x z).
Proof. exact (TRANS (@lem1720771 y x z) (@lem1720776 y x z)). Qed.
Lemma lem1720799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1720800 (y : real) (x : real) (z : real) : (term155 x y z) = (term156 y x z).
Proof. exact (MK_COMB (@lem1720799) (@lem1720798 y x z)). Qed.
Lemma lem1720822 (y : real) (x : real) (z : real) : (term154 y x z) = (term154 y x z).
Proof. exact (eq_refl (term154 y x z)). Qed.
Lemma lem1720823 (y : real) (x : real) (z : real) : ((term122 x y z) = (term154 y x z)) = ((term154 y x z) = (term154 y x z)).
Proof. exact (MK_COMB (@lem1720800 y x z) (@lem1720822 y x z)). Qed.
Lemma lem1720825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1720826 (x : Prop) : (x = x) = True.
Proof. exact (@lem1720825 Prop x). Qed.
Lemma lem1720827 (y : real) (x : real) (z : real) : ((term154 y x z) = (term154 y x z)) = True.
Proof. exact (@lem1720826 (term154 y x z)). Qed.
Lemma lem1720828 (y : real) (x : real) (z : real) : ((term122 x y z) = (term154 y x z)) = True.
Proof. exact (TRANS (@lem1720823 y x z) (@lem1720827 y x z)). Qed.
Lemma lem1720829 (y : real) (x : real) (z : real) : True = ((term122 x y z) = (term154 y x z)).
Proof. exact (SYM (@lem1720828 y x z)). Qed.
Lemma lem1720830 (y : real) (x : real) (z : real) : (term122 x y z) = (term154 y x z).
Proof. exact (EQ_MP (@lem1720829 y x z) (@lem0)). Qed.
Lemma lem1720831 (y : real) (x : real) (z : real) : term154 y x z.
Proof. exact (EQ_MP (@lem1720830 y x z) (@lem1720595 x y z)). Qed.
Lemma lem1720833 (b : Prop) (a : Prop) : (a \/ b) = (term132 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1720834 (x : real) (y : real) (z : real) : (term154 y x z) = (term157 x y z).
Proof. exact (@lem1720833 (term158 y x z) (y = z)). Qed.
Lemma lem1720836 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1720837 (y : real) (x : real) (z : real) : (term159 y x z) = (term160 y x z).
Proof. exact (@lem1720836 (term98 x y) (term98 x z)). Qed.
Lemma lem1720839 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1720840 (x : real) (y : real) : (term140 x y) = (x = y).
Proof. exact (@lem1720839 (x = y)). Qed.
Lemma lem1720841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1720842 (x : real) (y : real) : (term141 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1720841) (@lem1720840 x y)). Qed.
Lemma lem1720844 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1720845 (x : real) (z : real) : (term140 x z) = (x = z).
Proof. exact (@lem1720844 (x = z)). Qed.
Lemma lem1720846 (y : real) (x : real) (z : real) : (term160 y x z) = (term161 y x z).
Proof. exact (MK_COMB (@lem1720842 x y) (@lem1720845 x z)). Qed.
Lemma lem1720847 (y : real) (x : real) (z : real) : (term159 y x z) = (term161 y x z).
Proof. exact (TRANS (@lem1720837 y x z) (@lem1720846 y x z)). Qed.
Lemma lem1720848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1720849 (y : real) (x : real) (z : real) : (term162 y x z) = (term163 y x z).
Proof. exact (MK_COMB (@lem1720848) (@lem1720847 y x z)). Qed.
Lemma lem1720850 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1720851 (x : real) (y : real) (z : real) : (term157 x y z) = (term164 x y z).
Proof. exact (MK_COMB (@lem1720849 y x z) (@lem1720850 y z)). Qed.
Lemma lem1720852 (x : real) (y : real) (z : real) : (term154 y x z) = (term164 x y z).
Proof. exact (TRANS (@lem1720834 x y z) (@lem1720851 x y z)). Qed.
Lemma lem1720854 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : term165 y x.
Proof. exact (conj (@lem1720733 x y h2) (@lem1720741 x h1)). Qed.
Lemma lem1720856 (x : real) (y : real) (z : real) : term164 x y z.
Proof. exact (EQ_MP (@lem1720852 x y z) (@lem1720831 y x z)). Qed.
Lemma lem1720857 (y : real) (x : real) : term166 y x.
Proof. exact (@lem1720856 (term13 x) (term13 y) x). Qed.
Lemma lem1720860 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : (term13 y) = x.
Proof. exact (@lem1720857 y x (@lem1720854 x y h1 h2)). Qed.
Lemma lem1720861 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : term167 y x.
Proof. exact (fun h0 : term168 y x => @lem1720860 x y h1 h2). Qed.
Lemma lem1720863 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720864 (y : real) (x : real) : (term167 y x) = ((term13 y) = x).
Proof. exact (@lem1720863 ((term13 y) = x)). Qed.
Lemma lem1720865 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : (term13 y) = x.
Proof. exact (EQ_MP (@lem1720864 y x) (@lem1720861 x y h1 h2)). Qed.
Lemma lem1720867 (_26492 : real) (h1 : term10) : (term13 _26492) = _26492.
Proof. exact (EQ_MP (@lem1720345 _26492) (@lem1720344 _26492 h1)). Qed.
Lemma lem1720868 (y : real) (h1 : term10) : (term13 y) = y.
Proof. exact (@lem1720867 y h1). Qed.
Lemma lem1720869 (y : real) (h1 : term10) : term149 y.
Proof. exact (fun h0 : term150 y => @lem1720868 y h1). Qed.
Lemma lem1720871 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720872 (y : real) : (term149 y) = ((term13 y) = y).
Proof. exact (@lem1720871 ((term13 y) = y)). Qed.
Lemma lem1720873 (y : real) (h1 : term10) : (term13 y) = y.
Proof. exact (EQ_MP (@lem1720872 y) (@lem1720869 y h1)). Qed.
Lemma lem1720874 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : term169 x y.
Proof. exact (conj (@lem1720865 x y h1 h2) (@lem1720873 y h1)). Qed.
Lemma lem1720876 (x : real) (y : real) (z : real) : term164 x y z.
Proof. exact (EQ_MP (@lem1720852 x y z) (@lem1720831 y x z)). Qed.
Lemma lem1720877 (x : real) (y : real) : term170 x y.
Proof. exact (@lem1720876 (term13 y) x y). Qed.
Lemma lem1720880 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : x = y.
Proof. exact (@lem1720877 x y (@lem1720874 x y h1 h2)). Qed.
Lemma lem1720881 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : term171 x y.
Proof. exact (fun h0 : term98 x y => @lem1720880 x y h1 h2). Qed.
Lemma lem1720883 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720884 (x : real) (y : real) : (term171 x y) = (x = y).
Proof. exact (@lem1720883 (x = y)). Qed.
Lemma lem1720885 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : x = y.
Proof. exact (EQ_MP (@lem1720884 x y) (@lem1720881 x y h1 h2)). Qed.
Lemma lem1720888 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1720890 (x : real) (y : real) : (term98 x y) = (term172 x y).
Proof. exact (@lem1720888 (x = y)). Qed.
Lemma lem1720893 (x : real) (y : real) (h1 : term21 x y) : term172 x y.
Proof. exact (EQ_MP (@lem1720890 x y) (@lem1720362 x y h1)). Qed.
Lemma lem1720896 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : False.
Proof. exact (@lem1720893 x y h2 (@lem1720885 x y h1 h2)). Qed.
Lemma lem1720897 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : term114.
Proof. exact (fun h0 : ~ False => @lem1720896 x y h1 h2). Qed.
Lemma lem1720899 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1720900 : term114 = False.
Proof. exact (@lem1720899 False). Qed.
Lemma lem1720901 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : False.
Proof. exact (EQ_MP (@lem1720900) (@lem1720897 x y h1 h2)). Qed.
Lemma lem1720902 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720561) (@lem1720558 x y h1 h2)). Qed.
Lemma lem1720903 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720504) (@lem1720501 x y h1 h2)). Qed.
Lemma lem1720904 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : (term96 x y) = False.
Proof. exact (prop_ext (fun h3 : term96 x y => @lem1720902 x y h1 h2) (fun h3 : False => @lem1720358 x y h1)). Qed.
Lemma lem1720905 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720904 x y h1 h2) (@lem1720358 x y h1)). Qed.
Lemma lem1720906 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : (term95 x y) = False.
Proof. exact (prop_ext (fun h3 : term95 x y => @lem1720903 x y h1 h2) (fun h3 : False => @lem1720352 x y h1)). Qed.
Lemma lem1720907 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720906 x y h1 h2) (@lem1720352 x y h1)). Qed.
Lemma lem1720908 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : (term96 x y) = False.
Proof. exact (prop_ext (fun h3 : term96 x y => @lem1720905 x y h1 h2) (fun h3 : False => @lem1720318 x y h1)). Qed.
Lemma lem1720909 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720908 x y h1 h2) (@lem1720318 x y h1)). Qed.
Lemma lem1720910 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : (term95 x y) = False.
Proof. exact (prop_ext (fun h3 : term95 x y => @lem1720907 x y h1 h2) (fun h3 : False => @lem1720303 x y h1)). Qed.
Lemma lem1720911 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720910 x y h1 h2) (@lem1720303 x y h1)). Qed.
Lemma lem1720912 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1720901 x y h1 h2) (fun h3 : False => @lem1720325 h1)). Qed.
Lemma lem1720913 (x : real) (y : real) (h1 : term10) (h2 : term21 x y) : False.
Proof. exact (EQ_MP (@lem1720912 x y h1 h2) (@lem1720325 h1)). Qed.
Lemma lem1720914 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : (term96 x y) = False.
Proof. exact (prop_ext (fun h3 : term96 x y => @lem1720909 x y h1 h2) (fun h3 : False => @lem1720318 x y h1)). Qed.
Lemma lem1720915 (x : real) (y : real) (h1 : term96 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720914 x y h1 h2) (@lem1720318 x y h1)). Qed.
Lemma lem1720916 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : (term95 x y) = False.
Proof. exact (prop_ext (fun h3 : term95 x y => @lem1720911 x y h1 h2) (fun h3 : False => @lem1720303 x y h1)). Qed.
Lemma lem1720917 (x : real) (y : real) (h1 : term95 x y) (h2 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1720916 x y h1 h2) (@lem1720303 x y h1)). Qed.
Lemma lem1720918 (x : real) (y : real) (h1 : term24 x y) : False.
Proof. exact (or_elim (@lem1720281 x y h1) (fun h0 : term95 x y => @lem1720917 x y h0 h1) (fun h0 : term96 x y => @lem1720915 x y h0 h1)). Qed.
Lemma lem1720919 (x : real) (y : real) (h1 : term10) (h2 : term28 x y) : False.
Proof. exact (or_elim (@lem1720278 x y h2) (fun h0 : term24 x y => @lem1720918 x y h0) (fun h0 : term21 x y => @lem1720913 x y h1 h0)). Qed.
Lemma lem1720920 (x : real) (y : real) (h1 : term10) (h2 : term28 x y) : (term28 x y) = False.
Proof. exact (prop_ext (fun h3 : term28 x y => @lem1720919 x y h1 h2) (fun h3 : False => @lem1720278 x y h2)). Qed.
Lemma lem1720921 (x : real) (y : real) (h1 : term10) (h2 : term28 x y) : False.
Proof. exact (EQ_MP (@lem1720920 x y h1 h2) (@lem1720278 x y h2)). Qed.
Lemma lem1720922 (x : real) (y : real) (h1 : term10) (h2 : term28 x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1720921 x y h1 h2) (fun h3 : False => @lem1720210 h1)). Qed.
Lemma lem1720923 (x : real) (y : real) (h1 : term10) (h2 : term28 x y) : False.
Proof. exact (EQ_MP (@lem1720922 x y h1 h2) (@lem1720210 h1)). Qed.
Lemma lem1720924 (x : real) (h1 : term10) (h2 : term38 x) : False.
Proof. exact (ex_elim (@lem1720192 x h2) (fun y : real => fun h0 : term37 x y => @lem1720923 x y h1 h0)). Qed.
Lemma lem1720925 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem1720178 h2) (fun x : real => fun h0 : term43 x => @lem1720924 x h1 h0)). Qed.
Lemma lem1720926 (h1 : term10) (h2 : term3) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1720925 h1 h2) (fun h3 : False => @lem1720191 h1)). Qed.
Lemma lem1720927 (h1 : term10) (h2 : term3) : False.
Proof. exact (EQ_MP (@lem1720926 h1 h2) (@lem1720191 h1)). Qed.
Lemma lem1720928 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1720927 h0 h1). Qed.
Lemma lem1720929 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1720930 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem1720929) (@lem1720928 h1)). Qed.
Lemma lem1720931 : term12.
Proof. exact (fun h0 : term3 => @lem1720930 h0). Qed.
Lemma lem1720932 : term4.
Proof. exact (EQ_MP (@lem1719808) (@lem1720931)). Qed.
Lemma lem1720934 : term4.
Proof. exact (@lem1719729 (@lem1720932)). Qed.
Lemma lem1720935 (h1 : term3) : term8.
Proof. exact (@lem1720934 (@lem1719714 h1)). Qed.
Lemma lem1720936 (h1 : term3) : False.
Proof. exact (@lem1720935 h1 (@lem1717545)). Qed.
Lemma lem1720937 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1720936 h1) (fun h2 : False => @lem1719714 h1)). Qed.
Lemma lem1720938 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1720937 h1) (@lem1719714 h1)). Qed.
Lemma lem1720939 : term2.
Proof. exact (fun h0 : term3 => @lem1720938 h0). Qed.
Lemma lem1720940 : term1.
Proof. exact (EQ_MP (@lem1719713) (@lem1720939)). Qed.
