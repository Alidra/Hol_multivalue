Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LTE_ADD_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
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
Require Import thm69_spec.
Lemma lem1381642 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1381643 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1381644 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1381643 t1) (@lem1381642 t1)). Qed.
Lemma lem1381645 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1381644 t1 t2). Qed.
Lemma lem1381646 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1381647 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1381646 t1 t2) (@lem1381645 t1 t2)). Qed.
Lemma lem1381648 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1381647 t1 t2 t3). Qed.
Lemma lem1381649 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1381650 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1381649 t1 t2 t3) (@lem1381648 t1 t2 t3)). Qed.
Lemma lem1381651 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1381650 t1 t2 t3)). Qed.
Lemma lem1381653 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1381654 : term8 = term9.
Proof. exact (@lem1381653 term8). Qed.
Lemma lem1381655 : term9 = term8.
Proof. exact (SYM (@lem1381654)). Qed.
Lemma lem1381656 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1381659 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1381660 : term12.
Proof. exact (fun h0 : term11 => @lem1381659 h0). Qed.
Lemma lem1381661 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1381662 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1381663 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1381661 h2 (@lem1381662 h1)). Qed.
Lemma lem1381664 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1381663 h1 h0). Qed.
Lemma lem1381665 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1381666 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1381664 h1 (@lem1381665 h2)). Qed.
Lemma lem1381667 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1381666 h0 h1). Qed.
Lemma lem1381668 : term14.
Proof. exact (fun h0 : term12 => @lem1381667 h0). Qed.
Lemma lem1381671 : term12.
Proof. exact (@lem1381668 (@lem1381660)). Qed.
Lemma lem1381701 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1381702 : term15 = term16.
Proof. exact (@lem1381701 term17). Qed.
Lemma lem1381713 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1381714 : term19 = term20.
Proof. exact (MK_COMB (@lem1381713) (@lem1381702)). Qed.
Lemma lem1381717 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1381724 : term11 = term22.
Proof. exact (MK_COMB (@lem1381717) (@lem1381714)). Qed.
Lemma lem1381729 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1381730 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : real => @lem1381729 x y)). Qed.
Lemma lem1381731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381732 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1381731) (@lem1381730 x)). Qed.
Lemma lem1381733 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1381732 x)). Qed.
Lemma lem1381734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381735 : term17 = term17.
Proof. exact (MK_COMB (@lem1381734) (@lem1381733)). Qed.
Lemma lem1381736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1381737 : term16 = term16.
Proof. exact (MK_COMB (@lem1381736) (@lem1381735)). Qed.
Lemma lem1381746 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1381747 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1381746 x y)). Qed.
Lemma lem1381748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381749 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1381748) (@lem1381747 x)). Qed.
Lemma lem1381750 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1381749 x)). Qed.
Lemma lem1381751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381752 : term31 = term31.
Proof. exact (MK_COMB (@lem1381751) (@lem1381750)). Qed.
Lemma lem1381753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1381754 : term18 = term18.
Proof. exact (MK_COMB (@lem1381753) (@lem1381752)). Qed.
Lemma lem1381755 : term20 = term20.
Proof. exact (MK_COMB (@lem1381754) (@lem1381737)). Qed.
Lemma lem1381764 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1381765 (x : real) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : real => @lem1381764 x y)). Qed.
Lemma lem1381766 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381767 (x : real) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1381766) (@lem1381765 x)). Qed.
Lemma lem1381768 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1381767 x)). Qed.
Lemma lem1381769 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381770 : term8 = term8.
Proof. exact (MK_COMB (@lem1381769) (@lem1381768)). Qed.
Lemma lem1381771 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1381772 : term10 = term10.
Proof. exact (MK_COMB (@lem1381771) (@lem1381770)). Qed.
Lemma lem1381773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1381774 : term21 = term21.
Proof. exact (MK_COMB (@lem1381773) (@lem1381772)). Qed.
Lemma lem1381775 : term22 = term22.
Proof. exact (MK_COMB (@lem1381774) (@lem1381755)). Qed.
Lemma lem1381828 : term11 = term22.
Proof. exact (TRANS (@lem1381724) (@lem1381775)). Qed.
Lemma lem1381829 : term22 = term11.
Proof. exact (SYM (@lem1381828)). Qed.
Lemma lem1381830 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1381831 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1381832 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1381843 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (@lem17362 (term38 x y) (term39 x y)). Qed.
Lemma lem1381844 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1381845 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1381844 (term33 x)). Qed.
Lemma lem1381846 (x : real) (y : real) : (term44 x y) = (term32 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1381847 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1381848 (x : real) (y : real) : (term45 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1381847) (@lem1381846 x y)). Qed.
Lemma lem1381849 (x : real) (y : real) : (term45 x y) = (term37 x y).
Proof. exact (TRANS (@lem1381848 x y) (@lem1381843 x y)). Qed.
Lemma lem1381850 (x : real) : (term46 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem1381849 x y)). Qed.
Lemma lem1381851 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1381852 (x : real) : (term43 x) = (term48 x).
Proof. exact (MK_COMB (@lem1381851) (@lem1381850 x)). Qed.
Lemma lem1381853 (x : real) : (term42 x) = (term48 x).
Proof. exact (TRANS (@lem1381845 x) (@lem1381852 x)). Qed.
Lemma lem1381854 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1381855 : term10 = term49.
Proof. exact (@lem1381854 term35). Qed.
Lemma lem1381856 (x : real) : (term50 x) = (term34 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1381857 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1381858 (x : real) : (term51 x) = (term42 x).
Proof. exact (MK_COMB (@lem1381857) (@lem1381856 x)). Qed.
Lemma lem1381859 (x : real) : (term51 x) = (term48 x).
Proof. exact (TRANS (@lem1381858 x) (@lem1381853 x)). Qed.
Lemma lem1381860 : term52 = term53.
Proof. exact (fun_ext (fun x : real => @lem1381859 x)). Qed.
Lemma lem1381861 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1381862 : term49 = term54.
Proof. exact (MK_COMB (@lem1381861) (@lem1381860)). Qed.
Lemma lem1381919 : term10 = term54.
Proof. exact (TRANS (@lem1381855) (@lem1381862)). Qed.
Lemma lem1381920 (h1 : term10) : term54.
Proof. exact (EQ_MP (@lem1381919) (@lem1381830 h1)). Qed.
Lemma lem1381927 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (@lem17045 (term57 x) (term58 y)). Qed.
Lemma lem1381928 (x : real) (y : real) : (term39 x y) = (term39 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1381929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1381930 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1381929) (@lem1381927 x y)). Qed.
Lemma lem1381931 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1381930 x y) (@lem1381928 x y)). Qed.
Lemma lem1381932 (x : real) (y : real) : (term27 x y) = (term61 x y).
Proof. exact (@lem17265 (term63 x y) (term39 x y)). Qed.
Lemma lem1381933 (x : real) (y : real) : (term27 x y) = (term62 x y).
Proof. exact (TRANS (@lem1381932 x y) (@lem1381931 x y)). Qed.
Lemma lem1381934 (x : real) : (term28 x) = (term64 x).
Proof. exact (fun_ext (fun y : real => @lem1381933 x y)). Qed.
Lemma lem1381935 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381936 (x : real) : (term29 x) = (term65 x).
Proof. exact (MK_COMB (@lem1381935) (@lem1381934 x)). Qed.
Lemma lem1381937 : term30 = term66.
Proof. exact (fun_ext (fun x : real => @lem1381936 x)). Qed.
Lemma lem1381938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381995 : term31 = term67.
Proof. exact (MK_COMB (@lem1381938) (@lem1381937)). Qed.
Lemma lem1381996 (h1 : term31) : term67.
Proof. exact (EQ_MP (@lem1381995) (@lem1381831 h1)). Qed.
Lemma lem1382003 (x : real) (y : real) : (term23 x y) = (term68 x y).
Proof. exact (@lem17265 (real_lt x y) (real_le x y)). Qed.
Lemma lem1382004 (x : real) : (term24 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1382003 x y)). Qed.
Lemma lem1382005 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382006 (x : real) : (term25 x) = (term70 x).
Proof. exact (MK_COMB (@lem1382005) (@lem1382004 x)). Qed.
Lemma lem1382007 : term26 = term71.
Proof. exact (fun_ext (fun x : real => @lem1382006 x)). Qed.
Lemma lem1382008 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382065 : term17 = term72.
Proof. exact (MK_COMB (@lem1382008) (@lem1382007)). Qed.
Lemma lem1382066 (h1 : term17) : term72.
Proof. exact (EQ_MP (@lem1382065) (@lem1381832 h1)). Qed.
Lemma lem1382067 (x : real) (h1 : term48 x) : term48 x.
Proof. exact (h1). Qed.
Lemma lem1382109 (x : real) (y : real) : (term62 x y) = (term62 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1382110 (x : real) : (term64 x) = (term64 x).
Proof. exact (fun_ext (fun y : real => @lem1382109 x y)). Qed.
Lemma lem1382111 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382112 (x : real) : (term65 x) = (term65 x).
Proof. exact (MK_COMB (@lem1382111) (@lem1382110 x)). Qed.
Lemma lem1382113 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem1382112 x)). Qed.
Lemma lem1382114 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382115 : term67 = term67.
Proof. exact (MK_COMB (@lem1382114) (@lem1382113)). Qed.
Lemma lem1382116 (h1 : term31) : term67.
Proof. exact (EQ_MP (@lem1382115) (@lem1381996 h1)). Qed.
Lemma lem1382131 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1382132 (x : real) : (term69 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1382131 x y)). Qed.
Lemma lem1382133 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382134 (x : real) : (term70 x) = (term70 x).
Proof. exact (MK_COMB (@lem1382133) (@lem1382132 x)). Qed.
Lemma lem1382135 : term71 = term71.
Proof. exact (fun_ext (fun x : real => @lem1382134 x)). Qed.
Lemma lem1382136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382137 : term72 = term72.
Proof. exact (MK_COMB (@lem1382136) (@lem1382135)). Qed.
Lemma lem1382138 (h1 : term17) : term72.
Proof. exact (EQ_MP (@lem1382137) (@lem1382066 h1)). Qed.
Lemma lem1382178 (x : real) (y : real) (h1 : term37 x y) : term37 x y.
Proof. exact (h1). Qed.
Lemma lem1382180 (x : real) (y : real) (h1 : term37 x y) : term38 x y.
Proof. exact (proj1 (@lem1382178 x y h1)). Qed.
Lemma lem1382196 (x : real) (y : real) : (term62 x y) = (term62 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1382197 (x : real) : (term64 x) = (term64 x).
Proof. exact (fun_ext (fun y : real => @lem1382196 x y)). Qed.
Lemma lem1382198 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382199 (x : real) : (term65 x) = (term65 x).
Proof. exact (MK_COMB (@lem1382198) (@lem1382197 x)). Qed.
Lemma lem1382200 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem1382199 x)). Qed.
Lemma lem1382201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382203 : term67 = term67.
Proof. exact (MK_COMB (@lem1382201) (@lem1382200)). Qed.
Lemma lem1382204 (h1 : term31) : term67.
Proof. exact (EQ_MP (@lem1382203) (@lem1382116 h1)). Qed.
Lemma lem1382212 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1382213 (x : real) : (term69 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1382212 x y)). Qed.
Lemma lem1382214 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382215 (x : real) : (term70 x) = (term70 x).
Proof. exact (MK_COMB (@lem1382214) (@lem1382213 x)). Qed.
Lemma lem1382216 : term71 = term71.
Proof. exact (fun_ext (fun x : real => @lem1382215 x)). Qed.
Lemma lem1382217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382219 : term72 = term72.
Proof. exact (MK_COMB (@lem1382217) (@lem1382216)). Qed.
Lemma lem1382220 (h1 : term17) : term72.
Proof. exact (EQ_MP (@lem1382219) (@lem1382138 h1)). Qed.
Lemma lem1382233 (_24491 : real) (h1 : term31) : term73 _24491.
Proof. exact (@lem1382204 h1 _24491). Qed.
Lemma lem1382234 (_24491 : real) : (term73 _24491) = (term65 _24491).
Proof. exact (eq_refl (term73 _24491)). Qed.
Lemma lem1382235 (_24491 : real) (h1 : term31) : term65 _24491.
Proof. exact (EQ_MP (@lem1382234 _24491) (@lem1382233 _24491 h1)). Qed.
Lemma lem1382236 (_24491 : real) (_24492 : real) (h1 : term31) : term74 _24491 _24492.
Proof. exact (@lem1382235 _24491 h1 _24492). Qed.
Lemma lem1382237 (_24491 : real) (_24492 : real) : (term74 _24491 _24492) = (term62 _24491 _24492).
Proof. exact (eq_refl (term74 _24491 _24492)). Qed.
Lemma lem1382238 (_24491 : real) (_24492 : real) (h1 : term31) : term62 _24491 _24492.
Proof. exact (EQ_MP (@lem1382237 _24491 _24492) (@lem1382236 _24491 _24492 h1)). Qed.
Lemma lem1382239 (_24493 : real) (h1 : term17) : term75 _24493.
Proof. exact (@lem1382220 h1 _24493). Qed.
Lemma lem1382240 (_24493 : real) : (term75 _24493) = (term70 _24493).
Proof. exact (eq_refl (term75 _24493)). Qed.
Lemma lem1382241 (_24493 : real) (h1 : term17) : term70 _24493.
Proof. exact (EQ_MP (@lem1382240 _24493) (@lem1382239 _24493 h1)). Qed.
Lemma lem1382242 (_24493 : real) (_24494 : real) (h1 : term17) : term76 _24493 _24494.
Proof. exact (@lem1382241 _24493 h1 _24494). Qed.
Lemma lem1382243 (_24493 : real) (_24494 : real) : (term76 _24493 _24494) = (term68 _24493 _24494).
Proof. exact (eq_refl (term76 _24493 _24494)). Qed.
Lemma lem1382255 (_24491 : real) (_24492 : real) : (term62 _24491 _24492) = (term77 _24491 _24492).
Proof. exact (@lem1381651 (term78 _24491) (term79 _24492) (term39 _24491 _24492)). Qed.
Lemma lem1382256 (_24491 : real) (_24492 : real) (h1 : term31) : term77 _24491 _24492.
Proof. exact (EQ_MP (@lem1382255 _24491 _24492) (@lem1382238 _24491 _24492 h1)). Qed.
Lemma lem1382262 (_24493 : real) (_24494 : real) (h1 : term17) : term68 _24493 _24494.
Proof. exact (EQ_MP (@lem1382243 _24493 _24494) (@lem1382242 _24493 _24494 h1)). Qed.
Lemma lem1382264 (x : real) (y : real) (h1 : term37 x y) : term80 x y.
Proof. exact (proj2 (@lem1382178 x y h1)). Qed.
Lemma lem1382270 (x : real) (y : real) (h1 : term37 x y) : term57 x.
Proof. exact (proj1 (@lem1382180 x y h1)). Qed.
Lemma lem1382271 (x : real) (y : real) (h1 : term37 x y) : term81 x.
Proof. exact (fun h0 : term78 x => @lem1382270 x y h1). Qed.
Lemma lem1382273 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1382274 (x : real) : (term81 x) = (term57 x).
Proof. exact (@lem1382273 (term57 x)). Qed.
Lemma lem1382275 (x : real) (y : real) (h1 : term37 x y) : term57 x.
Proof. exact (EQ_MP (@lem1382274 x) (@lem1382271 x y h1)). Qed.
Lemma lem1382277 (x : real) (y : real) (h1 : term37 x y) : term57 y.
Proof. exact (proj2 (@lem1382180 x y h1)). Qed.
Lemma lem1382278 (x : real) (y : real) (h1 : term37 x y) : term81 y.
Proof. exact (fun h0 : term78 y => @lem1382277 x y h1). Qed.
Lemma lem1382280 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1382281 (y : real) : (term81 y) = (term57 y).
Proof. exact (@lem1382280 (term57 y)). Qed.
Lemma lem1382282 (x : real) (y : real) (h1 : term37 x y) : term57 y.
Proof. exact (EQ_MP (@lem1382281 y) (@lem1382278 x y h1)). Qed.
Lemma lem1382288 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1382289 (_24493 : real) (_24494 : real) : (term68 _24493 _24494) = (term83 _24493 _24494).
Proof. exact (@lem1382288 (real_le _24493 _24494) (term84 _24493 _24494)). Qed.
Lemma lem1382295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1382296 (_24493 : real) (_24494 : real) : (term85 _24493 _24494) = (term86 _24493 _24494).
Proof. exact (MK_COMB (@lem1382295) (@lem1382289 _24493 _24494)). Qed.
Lemma lem1382302 (_24493 : real) (_24494 : real) : (term83 _24493 _24494) = (term83 _24493 _24494).
Proof. exact (eq_refl (term83 _24493 _24494)). Qed.
Lemma lem1382303 (_24493 : real) (_24494 : real) : ((term68 _24493 _24494) = (term83 _24493 _24494)) = ((term83 _24493 _24494) = (term83 _24493 _24494)).
Proof. exact (MK_COMB (@lem1382296 _24493 _24494) (@lem1382302 _24493 _24494)). Qed.
Lemma lem1382305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1382306 (x : Prop) : (x = x) = True.
Proof. exact (@lem1382305 Prop x). Qed.
Lemma lem1382307 (_24493 : real) (_24494 : real) : ((term83 _24493 _24494) = (term83 _24493 _24494)) = True.
Proof. exact (@lem1382306 (term83 _24493 _24494)). Qed.
Lemma lem1382308 (_24493 : real) (_24494 : real) : ((term68 _24493 _24494) = (term83 _24493 _24494)) = True.
Proof. exact (TRANS (@lem1382303 _24493 _24494) (@lem1382307 _24493 _24494)). Qed.
Lemma lem1382309 (_24493 : real) (_24494 : real) : True = ((term68 _24493 _24494) = (term83 _24493 _24494)).
Proof. exact (SYM (@lem1382308 _24493 _24494)). Qed.
Lemma lem1382310 (_24493 : real) (_24494 : real) : (term68 _24493 _24494) = (term83 _24493 _24494).
Proof. exact (EQ_MP (@lem1382309 _24493 _24494) (@lem0)). Qed.
Lemma lem1382311 (_24493 : real) (_24494 : real) (h1 : term17) : term83 _24493 _24494.
Proof. exact (EQ_MP (@lem1382310 _24493 _24494) (@lem1382262 _24493 _24494 h1)). Qed.
Lemma lem1382313 (b : Prop) (a : Prop) : (a \/ b) = (term87 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1382314 (_24493 : real) (_24494 : real) : (term83 _24493 _24494) = (term88 _24493 _24494).
Proof. exact (@lem1382313 (term84 _24493 _24494) (real_le _24493 _24494)). Qed.
Lemma lem1382316 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1382317 (_24493 : real) (_24494 : real) : (term90 _24493 _24494) = (real_lt _24493 _24494).
Proof. exact (@lem1382316 (real_lt _24493 _24494)). Qed.
Lemma lem1382318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382319 (_24493 : real) (_24494 : real) : (term91 _24493 _24494) = (term92 _24493 _24494).
Proof. exact (MK_COMB (@lem1382318) (@lem1382317 _24493 _24494)). Qed.
Lemma lem1382320 (_24493 : real) (_24494 : real) : (real_le _24493 _24494) = (real_le _24493 _24494).
Proof. exact (eq_refl (real_le _24493 _24494)). Qed.
Lemma lem1382321 (_24493 : real) (_24494 : real) : (term88 _24493 _24494) = (term23 _24493 _24494).
Proof. exact (MK_COMB (@lem1382319 _24493 _24494) (@lem1382320 _24493 _24494)). Qed.
Lemma lem1382322 (_24493 : real) (_24494 : real) : (term83 _24493 _24494) = (term23 _24493 _24494).
Proof. exact (TRANS (@lem1382314 _24493 _24494) (@lem1382321 _24493 _24494)). Qed.
Lemma lem1382325 (_24493 : real) (_24494 : real) (h1 : term17) : term23 _24493 _24494.
Proof. exact (EQ_MP (@lem1382322 _24493 _24494) (@lem1382311 _24493 _24494 h1)). Qed.
Lemma lem1382326 (y : real) (h1 : term17) : term93 y.
Proof. exact (@lem1382325 term94 y h1). Qed.
Lemma lem1382329 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term58 y.
Proof. exact (@lem1382326 y h1 (@lem1382282 x y h2)). Qed.
Lemma lem1382330 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term95 y.
Proof. exact (fun h0 : term79 y => @lem1382329 x y h1 h2). Qed.
Lemma lem1382332 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1382333 (y : real) : (term95 y) = (term58 y).
Proof. exact (@lem1382332 (term58 y)). Qed.
Lemma lem1382334 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term58 y.
Proof. exact (EQ_MP (@lem1382333 y) (@lem1382330 x y h1 h2)). Qed.
Lemma lem1382340 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1382341 (_24491 : real) (_24492 : real) : (term77 _24491 _24492) = (term96 _24491 _24492).
Proof. exact (@lem1382340 (term79 _24492) (term78 _24491) (term39 _24491 _24492)). Qed.
Lemma lem1382355 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1382356 (_24492 : real) (_24491 : real) : (term97 _24491 _24492) = (term98 _24492 _24491).
Proof. exact (@lem1382355 (term39 _24491 _24492) (term78 _24491)). Qed.
Lemma lem1382362 (_24492 : real) : (term99 _24492) = (term99 _24492).
Proof. exact (eq_refl (term99 _24492)). Qed.
Lemma lem1382363 (_24492 : real) (_24491 : real) : (term96 _24491 _24492) = (term100 _24492 _24491).
Proof. exact (MK_COMB (@lem1382362 _24492) (@lem1382356 _24492 _24491)). Qed.
Lemma lem1382367 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1382368 (_24492 : real) (_24491 : real) : (term100 _24492 _24491) = (term101 _24492 _24491).
Proof. exact (@lem1382367 (term39 _24491 _24492) (term79 _24492) (term78 _24491)). Qed.
Lemma lem1382384 (_24492 : real) (_24491 : real) : (term96 _24491 _24492) = (term101 _24492 _24491).
Proof. exact (TRANS (@lem1382363 _24492 _24491) (@lem1382368 _24492 _24491)). Qed.
Lemma lem1382385 (_24492 : real) (_24491 : real) : (term77 _24491 _24492) = (term101 _24492 _24491).
Proof. exact (TRANS (@lem1382341 _24491 _24492) (@lem1382384 _24492 _24491)). Qed.
Lemma lem1382386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1382387 (_24492 : real) (_24491 : real) : (term102 _24491 _24492) = (term103 _24492 _24491).
Proof. exact (MK_COMB (@lem1382386) (@lem1382385 _24492 _24491)). Qed.
Lemma lem1382401 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1382402 (_24492 : real) (_24491 : real) : (term56 _24491 _24492) = (term104 _24492 _24491).
Proof. exact (@lem1382401 (term79 _24492) (term78 _24491)). Qed.
Lemma lem1382408 (_24491 : real) (_24492 : real) : (term105 _24491 _24492) = (term105 _24491 _24492).
Proof. exact (eq_refl (term105 _24491 _24492)). Qed.
Lemma lem1382409 (_24492 : real) (_24491 : real) : (term106 _24491 _24492) = (term101 _24492 _24491).
Proof. exact (MK_COMB (@lem1382408 _24491 _24492) (@lem1382402 _24492 _24491)). Qed.
Lemma lem1382420 (_24492 : real) (_24491 : real) : ((term77 _24491 _24492) = (term106 _24491 _24492)) = ((term101 _24492 _24491) = (term101 _24492 _24491)).
Proof. exact (MK_COMB (@lem1382387 _24492 _24491) (@lem1382409 _24492 _24491)). Qed.
Lemma lem1382422 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1382423 (x : Prop) : (x = x) = True.
Proof. exact (@lem1382422 Prop x). Qed.
Lemma lem1382424 (_24492 : real) (_24491 : real) : ((term101 _24492 _24491) = (term101 _24492 _24491)) = True.
Proof. exact (@lem1382423 (term101 _24492 _24491)). Qed.
Lemma lem1382425 (_24491 : real) (_24492 : real) : ((term77 _24491 _24492) = (term106 _24491 _24492)) = True.
Proof. exact (TRANS (@lem1382420 _24492 _24491) (@lem1382424 _24492 _24491)). Qed.
Lemma lem1382426 (_24491 : real) (_24492 : real) : True = ((term77 _24491 _24492) = (term106 _24491 _24492)).
Proof. exact (SYM (@lem1382425 _24491 _24492)). Qed.
Lemma lem1382427 (_24491 : real) (_24492 : real) : (term77 _24491 _24492) = (term106 _24491 _24492).
Proof. exact (EQ_MP (@lem1382426 _24491 _24492) (@lem0)). Qed.
Lemma lem1382428 (_24491 : real) (_24492 : real) (h1 : term31) : term106 _24491 _24492.
Proof. exact (EQ_MP (@lem1382427 _24491 _24492) (@lem1382256 _24491 _24492 h1)). Qed.
Lemma lem1382430 (b : Prop) (a : Prop) : (a \/ b) = (term87 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1382431 (_24491 : real) (_24492 : real) : (term106 _24491 _24492) = (term107 _24491 _24492).
Proof. exact (@lem1382430 (term56 _24491 _24492) (term39 _24491 _24492)). Qed.
Lemma lem1382433 (a : Prop) (b : Prop) : (term108 a b) = (term109 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1382434 (_24491 : real) (_24492 : real) : (term110 _24491 _24492) = (term111 _24491 _24492).
Proof. exact (@lem1382433 (term78 _24491) (term79 _24492)). Qed.
Lemma lem1382436 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1382437 (_24491 : real) : (term112 _24491) = (term57 _24491).
Proof. exact (@lem1382436 (term57 _24491)). Qed.
Lemma lem1382438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1382439 (_24491 : real) : (term113 _24491) = (term114 _24491).
Proof. exact (MK_COMB (@lem1382438) (@lem1382437 _24491)). Qed.
Lemma lem1382441 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1382442 (_24492 : real) : (term115 _24492) = (term58 _24492).
Proof. exact (@lem1382441 (term58 _24492)). Qed.
Lemma lem1382443 (_24491 : real) (_24492 : real) : (term111 _24491 _24492) = (term63 _24491 _24492).
Proof. exact (MK_COMB (@lem1382439 _24491) (@lem1382442 _24492)). Qed.
Lemma lem1382444 (_24491 : real) (_24492 : real) : (term110 _24491 _24492) = (term63 _24491 _24492).
Proof. exact (TRANS (@lem1382434 _24491 _24492) (@lem1382443 _24491 _24492)). Qed.
Lemma lem1382445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382446 (_24491 : real) (_24492 : real) : (term116 _24491 _24492) = (term117 _24491 _24492).
Proof. exact (MK_COMB (@lem1382445) (@lem1382444 _24491 _24492)). Qed.
Lemma lem1382447 (_24491 : real) (_24492 : real) : (term39 _24491 _24492) = (term39 _24491 _24492).
Proof. exact (eq_refl (term39 _24491 _24492)). Qed.
Lemma lem1382448 (_24491 : real) (_24492 : real) : (term107 _24491 _24492) = (term27 _24491 _24492).
Proof. exact (MK_COMB (@lem1382446 _24491 _24492) (@lem1382447 _24491 _24492)). Qed.
Lemma lem1382449 (_24491 : real) (_24492 : real) : (term106 _24491 _24492) = (term27 _24491 _24492).
Proof. exact (TRANS (@lem1382431 _24491 _24492) (@lem1382448 _24491 _24492)). Qed.
Lemma lem1382451 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term63 x y.
Proof. exact (conj (@lem1382275 x y h2) (@lem1382334 x y h1 h2)). Qed.
Lemma lem1382453 (_24491 : real) (_24492 : real) (h1 : term31) : term27 _24491 _24492.
Proof. exact (EQ_MP (@lem1382449 _24491 _24492) (@lem1382428 _24491 _24492 h1)). Qed.
Lemma lem1382454 (x : real) (y : real) (h1 : term31) : term27 x y.
Proof. exact (@lem1382453 x y h1). Qed.
Lemma lem1382457 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : term39 x y.
Proof. exact (@lem1382454 x y h1 (@lem1382451 x y h2 h3)). Qed.
Lemma lem1382458 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : term118 x y.
Proof. exact (fun h0 : term80 x y => @lem1382457 x y h1 h2 h3). Qed.
Lemma lem1382460 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1382461 (x : real) (y : real) : (term118 x y) = (term39 x y).
Proof. exact (@lem1382460 (term39 x y)). Qed.
Lemma lem1382462 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : term39 x y.
Proof. exact (EQ_MP (@lem1382461 x y) (@lem1382458 x y h1 h2 h3)). Qed.
Lemma lem1382465 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1382467 (x : real) (y : real) : (term80 x y) = (term119 x y).
Proof. exact (@lem1382465 (term39 x y)). Qed.
Lemma lem1382470 (x : real) (y : real) (h1 : term37 x y) : term119 x y.
Proof. exact (EQ_MP (@lem1382467 x y) (@lem1382264 x y h1)). Qed.
Lemma lem1382473 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : False.
Proof. exact (@lem1382470 x y h3 (@lem1382462 x y h1 h2 h3)). Qed.
Lemma lem1382474 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : term120.
Proof. exact (fun h0 : ~ False => @lem1382473 x y h1 h2 h3). Qed.
Lemma lem1382476 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1382477 : term120 = False.
Proof. exact (@lem1382476 False). Qed.
Lemma lem1382478 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1382477) (@lem1382474 x y h1 h2 h3)). Qed.
Lemma lem1382479 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : (term37 x y) = False.
Proof. exact (prop_ext (fun h4 : term37 x y => @lem1382478 x y h1 h2 h3) (fun h4 : False => @lem1382178 x y h3)). Qed.
Lemma lem1382480 (x : real) (y : real) (h1 : term31) (h2 : term17) (h3 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1382479 x y h1 h2 h3) (@lem1382178 x y h3)). Qed.
Lemma lem1382481 (x : real) (h1 : term31) (h2 : term17) (h3 : term48 x) : False.
Proof. exact (ex_elim (@lem1382067 x h3) (fun y : real => fun h0 : term47 x y => @lem1382480 x y h1 h2 h0)). Qed.
Lemma lem1382482 (h1 : term31) (h2 : term17) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1381920 h3) (fun x : real => fun h0 : term53 x => @lem1382481 x h1 h2 h0)). Qed.
Lemma lem1382483 (h1 : term31) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1382482 h1 h0 h2). Qed.
Lemma lem1382484 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1382485 (h1 : term31) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1382484) (@lem1382483 h1 h2)). Qed.
Lemma lem1382486 (h1 : term10) : term20.
Proof. exact (fun h0 : term31 => @lem1382485 h0 h1). Qed.
Lemma lem1382487 : term22.
Proof. exact (fun h0 : term10 => @lem1382486 h0). Qed.
Lemma lem1382488 : term11.
Proof. exact (EQ_MP (@lem1381829) (@lem1382487)). Qed.
Lemma lem1382490 : term11.
Proof. exact (@lem1381671 (@lem1382488)). Qed.
Lemma lem1382491 (h1 : term10) : term19.
Proof. exact (@lem1382490 (@lem1381656 h1)). Qed.
Lemma lem1382492 (h1 : term10) : term15.
Proof. exact (@lem1382491 h1 (@lem1380653)). Qed.
Lemma lem1382493 (h1 : term10) : False.
Proof. exact (@lem1382492 h1 (@lem1369133)). Qed.
Lemma lem1382494 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1382493 h1) (fun h2 : False => @lem1381656 h1)). Qed.
Lemma lem1382495 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1382494 h1) (@lem1381656 h1)). Qed.
Lemma lem1382496 : term9.
Proof. exact (fun h0 : term10 => @lem1382495 h0). Qed.
Lemma lem1382497 : term8.
Proof. exact (EQ_MP (@lem1381655) (@lem1382496)). Qed.
