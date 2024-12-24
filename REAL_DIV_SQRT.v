Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_SQRT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_EQ_LDIV_EQ_spec.
Require Import REAL_LE_LT_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_0_spec.
Require Import SQRT_POS_LT_spec.
Require Import SQRT_POW_2_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1964710 (x : real) (h1 : (term0 x) = (real_mul x x)) : (term0 x) = (real_mul x x).
Proof. exact (h1). Qed.
Lemma lem1964711 (x : real) (h1 : (term0 x) = (real_mul x x)) : (real_mul x x) = (term0 x).
Proof. exact (SYM (@lem1964710 x h1)). Qed.
Lemma lem1964712 (x : real) (h1 : (real_mul x x) = (term0 x)) : (real_mul x x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1964713 (x : real) (h1 : (real_mul x x) = (term0 x)) : (term0 x) = (real_mul x x).
Proof. exact (SYM (@lem1964712 x h1)). Qed.
Lemma lem1964714 (x : real) : ((term0 x) = (real_mul x x)) = ((real_mul x x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (real_mul x x) => @lem1964711 x h1) (fun h1 : (real_mul x x) = (term0 x) => @lem1964713 x h1)). Qed.
Lemma lem1964715 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1964714 x)). Qed.
Lemma lem1964716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964717 : term3 = term4.
Proof. exact (MK_COMB (@lem1964716) (@lem1964715)). Qed.
Lemma lem1964718 : term4.
Proof. exact (EQ_MP (@lem1964717) (@lem1383497)). Qed.
Lemma lem1964729 (x : real) : term5 x.
Proof. exact (@lem1376325 x). Qed.
Lemma lem1964730 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1964731 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1964730 x) (@lem1964729 x)). Qed.
Lemma lem1964732 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1964731 x y). Qed.
Lemma lem1964733 (x : real) (y : real) : (term7 x y) = ((real_le x y) = (term8 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1964742 (x : real) (y : real) : (real_le x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1964733 x y) (@lem1964732 x y)). Qed.
Lemma lem1964743 (x : real) : (term9 x) = (term10 x).
Proof. exact (@lem1964742 term11 x). Qed.
Lemma lem1964748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964749 (x : real) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem1964748) (@lem1964743 x)). Qed.
Lemma lem1964752 (x : real) : ((term14 x) = (sqrt x)) = ((term14 x) = (sqrt x)).
Proof. exact (eq_refl ((term14 x) = (sqrt x))). Qed.
Lemma lem1964753 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1964749 x) (@lem1964752 x)). Qed.
Lemma lem1964756 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem1964753 x)). Qed.
Lemma lem1964757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964758 : term19 = term20.
Proof. exact (MK_COMB (@lem1964757) (@lem1964756)). Qed.
Lemma lem1964763 : term20 = term19.
Proof. exact (SYM (@lem1964758)). Qed.
Lemma lem1964764 (x : real) (h1 : term10 x) : term10 x.
Proof. exact (h1). Qed.
Lemma lem1964765 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (h1). Qed.
Lemma lem1964766 (x : real) (h1 : term11 = x) : term11 = x.
Proof. exact (h1). Qed.
Lemma lem1964768 (p : Prop) : p = (term22 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1964769 (x : real) : ((term14 x) = (sqrt x)) = (term23 x).
Proof. exact (@lem1964768 ((term14 x) = (sqrt x))). Qed.
Lemma lem1964770 (x : real) : (term23 x) = ((term14 x) = (sqrt x)).
Proof. exact (SYM (@lem1964769 x)). Qed.
Lemma lem1964771 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1964774 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1964775 (x : real) : term26 x.
Proof. exact (fun h0 : term25 x => @lem1964774 x h0). Qed.
Lemma lem1964776 (x : real) (h1 : term26 x) : term26 x.
Proof. exact (h1). Qed.
Lemma lem1964777 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1964778 (x : real) (h1 : term25 x) (h2 : term26 x) : term25 x.
Proof. exact (@lem1964776 x h2 (@lem1964777 x h1)). Qed.
Lemma lem1964779 (x : real) (h1 : term25 x) : term27 x.
Proof. exact (fun h0 : term26 x => @lem1964778 x h1 h0). Qed.
Lemma lem1964780 (x : real) (h1 : term26 x) : term26 x.
Proof. exact (h1). Qed.
Lemma lem1964781 (x : real) (h1 : term25 x) (h2 : term26 x) : term25 x.
Proof. exact (@lem1964779 x h1 (@lem1964780 x h2)). Qed.
Lemma lem1964782 (x : real) (h1 : term26 x) : term26 x.
Proof. exact (fun h0 : term25 x => @lem1964781 x h0 h1). Qed.
Lemma lem1964783 (x : real) : term28 x.
Proof. exact (fun h0 : term26 x => @lem1964782 x h0). Qed.
Lemma lem1964786 (x : real) : term26 x.
Proof. exact (@lem1964783 x (@lem1964775 x)). Qed.
Lemma lem1964812 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1964813 : term29 = term30.
Proof. exact (@lem1964812 (term31 = term11)). Qed.
Lemma lem1964814 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1964815 : term33 = term34.
Proof. exact (MK_COMB (@lem1964814) (@lem1964813)). Qed.
Lemma lem1964818 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1964819 : term36 = term37.
Proof. exact (MK_COMB (@lem1964818) (@lem1964815)). Qed.
Lemma lem1964822 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1964823 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1964822 x) (@lem1964819)). Qed.
Lemma lem1964826 (x : real) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1964827 (x : real) : (term25 x) = (term42 x).
Proof. exact (MK_COMB (@lem1964826 x) (@lem1964823 x)). Qed.
Lemma lem1964830 : term43 = term44.
Proof. exact (fun_ext (fun x : real => @lem1964827 x)). Qed.
Lemma lem1964831 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964840 : term45 = term46.
Proof. exact (MK_COMB (@lem1964831) (@lem1964830)). Qed.
Lemma lem1964843 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1964844 (x : real) (y : real) : ((real_div x y) = (term47 x y)) = ((real_div x y) = (term47 x y)).
Proof. exact (eq_refl ((real_div x y) = (term47 x y))). Qed.
Lemma lem1964845 (x : real) : (term48 x) = (term48 x).
Proof. exact (fun_ext (fun y : real => @lem1964844 x y)). Qed.
Lemma lem1964846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964847 (x : real) : (term49 x) = (term49 x).
Proof. exact (MK_COMB (@lem1964846) (@lem1964845 x)). Qed.
Lemma lem1964848 : term50 = term50.
Proof. exact (fun_ext (fun x : real => @lem1964847 x)). Qed.
Lemma lem1964849 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964850 : term51 = term51.
Proof. exact (MK_COMB (@lem1964849) (@lem1964848)). Qed.
Lemma lem1964851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964852 : term32 = term32.
Proof. exact (MK_COMB (@lem1964851) (@lem1964850)). Qed.
Lemma lem1964853 : term34 = term34.
Proof. exact (MK_COMB (@lem1964852) (@lem1964843)). Qed.
Lemma lem1964854 (x : real) : ((term52 x) = term11) = ((term52 x) = term11).
Proof. exact (eq_refl ((term52 x) = term11)). Qed.
Lemma lem1964855 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1964854 x)). Qed.
Lemma lem1964856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964857 : term54 = term54.
Proof. exact (MK_COMB (@lem1964856) (@lem1964855)). Qed.
Lemma lem1964858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964859 : term35 = term35.
Proof. exact (MK_COMB (@lem1964858) (@lem1964857)). Qed.
Lemma lem1964860 : term37 = term37.
Proof. exact (MK_COMB (@lem1964859) (@lem1964853)). Qed.
Lemma lem1964865 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1964866 (x : real) : (term40 x) = (term40 x).
Proof. exact (MK_COMB (@lem1964865 x) (@lem1964860)). Qed.
Lemma lem1964869 (x : real) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1964870 (x : real) : (term42 x) = (term42 x).
Proof. exact (MK_COMB (@lem1964869 x) (@lem1964866 x)). Qed.
Lemma lem1964871 : term44 = term44.
Proof. exact (fun_ext (fun x : real => @lem1964870 x)). Qed.
Lemma lem1964872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964873 : term46 = term46.
Proof. exact (MK_COMB (@lem1964872) (@lem1964871)). Qed.
Lemma lem1964908 : term45 = term46.
Proof. exact (TRANS (@lem1964840) (@lem1964873)). Qed.
Lemma lem1964909 : term46 = term45.
Proof. exact (SYM (@lem1964908)). Qed.
Lemma lem1964912 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1964913 (h1 : term51) : term51.
Proof. exact (h1). Qed.
Lemma lem1964920 (x : real) (h1 : term11 = x) : term11 = x.
Proof. exact (h1). Qed.
Lemma lem1964926 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1964927 (x : real) : ((term52 x) = term11) = ((term52 x) = term11).
Proof. exact (eq_refl ((term52 x) = term11)). Qed.
Lemma lem1964928 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1964927 x)). Qed.
Lemma lem1964929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964938 : term54 = term54.
Proof. exact (MK_COMB (@lem1964929) (@lem1964928)). Qed.
Lemma lem1964939 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem1964938) (@lem1964912 h1)). Qed.
Lemma lem1964940 (x : real) (y : real) : ((real_div x y) = (term47 x y)) = ((real_div x y) = (term47 x y)).
Proof. exact (eq_refl ((real_div x y) = (term47 x y))). Qed.
Lemma lem1964941 (x : real) : (term48 x) = (term48 x).
Proof. exact (fun_ext (fun y : real => @lem1964940 x y)). Qed.
Lemma lem1964942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964943 (x : real) : (term49 x) = (term49 x).
Proof. exact (MK_COMB (@lem1964942) (@lem1964941 x)). Qed.
Lemma lem1964944 : term50 = term50.
Proof. exact (fun_ext (fun x : real => @lem1964943 x)). Qed.
Lemma lem1964945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1964958 : term51 = term51.
Proof. exact (MK_COMB (@lem1964945) (@lem1964944)). Qed.
Lemma lem1964959 (h1 : term51) : term51.
Proof. exact (EQ_MP (@lem1964958) (@lem1964913 h1)). Qed.
Lemma lem1964965 (h1 : term31 = term11) : term31 = term11.
Proof. exact (h1). Qed.
Lemma lem1964975 (x : real) (h1 : term11 = x) : term11 = x.
Proof. exact (h1). Qed.
Lemma lem1964991 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1965008 (x : real) : ((term52 x) = term11) = ((term52 x) = term11).
Proof. exact (eq_refl ((term52 x) = term11)). Qed.
Lemma lem1965009 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1965008 x)). Qed.
Lemma lem1965010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965011 : term54 = term54.
Proof. exact (MK_COMB (@lem1965010) (@lem1965009)). Qed.
Lemma lem1965012 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem1965011) (@lem1964939 h1)). Qed.
Lemma lem1965027 (x : real) (y : real) : ((real_div x y) = (term47 x y)) = ((real_div x y) = (term47 x y)).
Proof. exact (eq_refl ((real_div x y) = (term47 x y))). Qed.
Lemma lem1965028 (x : real) : (term48 x) = (term48 x).
Proof. exact (fun_ext (fun y : real => @lem1965027 x y)). Qed.
Lemma lem1965029 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965030 (x : real) : (term49 x) = (term49 x).
Proof. exact (MK_COMB (@lem1965029) (@lem1965028 x)). Qed.
Lemma lem1965031 : term50 = term50.
Proof. exact (fun_ext (fun x : real => @lem1965030 x)). Qed.
Lemma lem1965032 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965033 : term51 = term51.
Proof. exact (MK_COMB (@lem1965032) (@lem1965031)). Qed.
Lemma lem1965034 (h1 : term51) : term51.
Proof. exact (EQ_MP (@lem1965033) (@lem1964959 h1)). Qed.
Lemma lem1965050 (h1 : term31 = term11) : term31 = term11.
Proof. exact (h1). Qed.
Lemma lem1965054 (x : real) (h1 : term11 = x) : term11 = x.
Proof. exact (h1). Qed.
Lemma lem1965058 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1965060 (x : real) : ((term52 x) = term11) = ((term52 x) = term11).
Proof. exact (eq_refl ((term52 x) = term11)). Qed.
Lemma lem1965061 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1965060 x)). Qed.
Lemma lem1965062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965064 : term54 = term54.
Proof. exact (MK_COMB (@lem1965062) (@lem1965061)). Qed.
Lemma lem1965065 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem1965064) (@lem1965012 h1)). Qed.
Lemma lem1965067 (x : real) (y : real) : ((real_div x y) = (term47 x y)) = ((real_div x y) = (term47 x y)).
Proof. exact (eq_refl ((real_div x y) = (term47 x y))). Qed.
Lemma lem1965068 (x : real) : (term48 x) = (term48 x).
Proof. exact (fun_ext (fun y : real => @lem1965067 x y)). Qed.
Lemma lem1965069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965070 (x : real) : (term49 x) = (term49 x).
Proof. exact (MK_COMB (@lem1965069) (@lem1965068 x)). Qed.
Lemma lem1965071 : term50 = term50.
Proof. exact (fun_ext (fun x : real => @lem1965070 x)). Qed.
Lemma lem1965072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965074 : term51 = term51.
Proof. exact (MK_COMB (@lem1965072) (@lem1965071)). Qed.
Lemma lem1965075 (h1 : term51) : term51.
Proof. exact (EQ_MP (@lem1965074) (@lem1965034 h1)). Qed.
Lemma lem1965079 (h1 : term31 = term11) : term31 = term11.
Proof. exact (h1). Qed.
Lemma lem1965080 (_27610 : real) (h1 : term54) : term55 _27610.
Proof. exact (@lem1965065 h1 _27610). Qed.
Lemma lem1965081 (_27610 : real) : (term55 _27610) = ((term52 _27610) = term11).
Proof. exact (eq_refl (term55 _27610)). Qed.
Lemma lem1965083 (_27611 : real) (h1 : term51) : term56 _27611.
Proof. exact (@lem1965075 h1 _27611). Qed.
Lemma lem1965084 (_27611 : real) : (term56 _27611) = (term49 _27611).
Proof. exact (eq_refl (term56 _27611)). Qed.
Lemma lem1965085 (_27611 : real) (h1 : term51) : term49 _27611.
Proof. exact (EQ_MP (@lem1965084 _27611) (@lem1965083 _27611 h1)). Qed.
Lemma lem1965086 (_27611 : real) (_27612 : real) (h1 : term51) : term57 _27611 _27612.
Proof. exact (@lem1965085 _27611 h1 _27612). Qed.
Lemma lem1965087 (_27611 : real) (_27612 : real) : (term57 _27611 _27612) = ((real_div _27611 _27612) = (term47 _27611 _27612)).
Proof. exact (eq_refl (term57 _27611 _27612)). Qed.
Lemma lem1965090 (x : real) (h1 : term11 = x) : term11 = x.
Proof. exact (h1). Qed.
Lemma lem1965092 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1965098 (h1 : term31 = term11) : term31 = term11.
Proof. exact (h1). Qed.
Lemma lem1965099 (x : real) (h1 : term11 = x) : x = term11.
Proof. exact (SYM (@lem1965090 x h1)). Qed.
Lemma lem1965114 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1965115 (x : real) (h1 : term11 = x) : (term59 x) = term60.
Proof. exact (MK_COMB (@lem1965114) (@lem1965099 x h1)). Qed.
Lemma lem1965116 : term60 = term61.
Proof. exact (eq_refl term60). Qed.
Lemma lem1965117 (x : real) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1965118 (x : real) : ((term59 x) = term60) = ((term59 x) = term61).
Proof. exact (MK_COMB (@lem1965117 x) (@lem1965116)). Qed.
Lemma lem1965119 (x : real) : (term59 x) = (term24 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1965120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1965121 (x : real) : (term62 x) = (term63 x).
Proof. exact (MK_COMB (@lem1965120) (@lem1965119 x)). Qed.
Lemma lem1965122 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1965123 (x : real) : ((term59 x) = term61) = ((term24 x) = term61).
Proof. exact (MK_COMB (@lem1965121 x) (@lem1965122)). Qed.
Lemma lem1965124 (x : real) : ((term59 x) = term60) = ((term24 x) = term61).
Proof. exact (TRANS (@lem1965118 x) (@lem1965123 x)). Qed.
Lemma lem1965125 (x : real) (h1 : term11 = x) : (term24 x) = term61.
Proof. exact (EQ_MP (@lem1965124 x) (@lem1965115 x h1)). Qed.
Lemma lem1965126 (x : real) (h1 : term24 x) (h2 : term11 = x) : term61.
Proof. exact (EQ_MP (@lem1965125 x h2) (@lem1965092 x h1)). Qed.
Lemma lem1965168 (h1 : term31 = term11) : term31 = term11.
Proof. exact (h1). Qed.
Lemma lem1965232 (x : real) (y : real) (z : real) : term64 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1965236 (_27610 : real) (h1 : term54) : (term52 _27610) = term11.
Proof. exact (EQ_MP (@lem1965081 _27610) (@lem1965080 _27610 h1)). Qed.
Lemma lem1965237 (h1 : term54) : term65 = term11.
Proof. exact (@lem1965236 term66 h1). Qed.
Lemma lem1965238 (h1 : term54) : term67.
Proof. exact (fun h0 : term68 => @lem1965237 h1). Qed.
Lemma lem1965240 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965241 : term67 = (term65 = term11).
Proof. exact (@lem1965240 (term65 = term11)). Qed.
Lemma lem1965242 (h1 : term54) : term65 = term11.
Proof. exact (EQ_MP (@lem1965241) (@lem1965238 h1)). Qed.
Lemma lem1965244 (_27611 : real) (_27612 : real) (h1 : term51) : (real_div _27611 _27612) = (term47 _27611 _27612).
Proof. exact (EQ_MP (@lem1965087 _27611 _27612) (@lem1965086 _27611 _27612 h1)). Qed.
Lemma lem1965245 (h1 : term51) : term70 = term65.
Proof. exact (@lem1965244 term11 term31 h1). Qed.
Lemma lem1965246 (h1 : term51) : term71.
Proof. exact (fun h0 : term72 => @lem1965245 h1). Qed.
Lemma lem1965248 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965249 : term71 = (term70 = term65).
Proof. exact (@lem1965248 (term70 = term65)). Qed.
Lemma lem1965250 (h1 : term51) : term70 = term65.
Proof. exact (EQ_MP (@lem1965249) (@lem1965246 h1)). Qed.
Lemma lem1965252 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1965253 : term70 = term70.
Proof. exact (@lem1965252 term70). Qed.
Lemma lem1965254 : term73.
Proof. exact (fun h0 : term74 => @lem1965253). Qed.
Lemma lem1965256 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965257 : term73 = (term70 = term70).
Proof. exact (@lem1965256 (term70 = term70)). Qed.
Lemma lem1965258 : term70 = term70.
Proof. exact (EQ_MP (@lem1965257) (@lem1965254)). Qed.
Lemma lem1965276 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1965277 (y : real) (x : real) (z : real) : (term75 x y z) = (term76 y x z).
Proof. exact (@lem1965276 (y = z) (term77 x z)). Qed.
Lemma lem1965287 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1965288 (y : real) (x : real) (z : real) : (term64 x y z) = (term79 y x z).
Proof. exact (MK_COMB (@lem1965287 x y) (@lem1965277 y x z)). Qed.
Lemma lem1965292 (q : Prop) (p : Prop) (r : Prop) : (term80 p q r) = (term80 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1965293 (y : real) (x : real) (z : real) : (term79 y x z) = (term81 y x z).
Proof. exact (@lem1965292 (y = z) (term77 x y) (term77 x z)). Qed.
Lemma lem1965315 (y : real) (x : real) (z : real) : (term64 x y z) = (term81 y x z).
Proof. exact (TRANS (@lem1965288 y x z) (@lem1965293 y x z)). Qed.
Lemma lem1965316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1965317 (y : real) (x : real) (z : real) : (term82 x y z) = (term83 y x z).
Proof. exact (MK_COMB (@lem1965316) (@lem1965315 y x z)). Qed.
Lemma lem1965339 (y : real) (x : real) (z : real) : (term81 y x z) = (term81 y x z).
Proof. exact (eq_refl (term81 y x z)). Qed.
Lemma lem1965340 (y : real) (x : real) (z : real) : ((term64 x y z) = (term81 y x z)) = ((term81 y x z) = (term81 y x z)).
Proof. exact (MK_COMB (@lem1965317 y x z) (@lem1965339 y x z)). Qed.
Lemma lem1965342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1965343 (x : Prop) : (x = x) = True.
Proof. exact (@lem1965342 Prop x). Qed.
Lemma lem1965344 (y : real) (x : real) (z : real) : ((term81 y x z) = (term81 y x z)) = True.
Proof. exact (@lem1965343 (term81 y x z)). Qed.
Lemma lem1965345 (y : real) (x : real) (z : real) : ((term64 x y z) = (term81 y x z)) = True.
Proof. exact (TRANS (@lem1965340 y x z) (@lem1965344 y x z)). Qed.
Lemma lem1965346 (y : real) (x : real) (z : real) : True = ((term64 x y z) = (term81 y x z)).
Proof. exact (SYM (@lem1965345 y x z)). Qed.
Lemma lem1965347 (y : real) (x : real) (z : real) : (term64 x y z) = (term81 y x z).
Proof. exact (EQ_MP (@lem1965346 y x z) (@lem0)). Qed.
Lemma lem1965348 (y : real) (x : real) (z : real) : term81 y x z.
Proof. exact (EQ_MP (@lem1965347 y x z) (@lem1965232 x y z)). Qed.
Lemma lem1965350 (b : Prop) (a : Prop) : (a \/ b) = (term84 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1965351 (x : real) (y : real) (z : real) : (term81 y x z) = (term85 x y z).
Proof. exact (@lem1965350 (term86 y x z) (y = z)). Qed.
Lemma lem1965353 (a : Prop) (b : Prop) : (term87 a b) = (term88 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1965354 (y : real) (x : real) (z : real) : (term89 y x z) = (term90 y x z).
Proof. exact (@lem1965353 (term77 x y) (term77 x z)). Qed.
Lemma lem1965356 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1965357 (x : real) (y : real) : (term92 x y) = (x = y).
Proof. exact (@lem1965356 (x = y)). Qed.
Lemma lem1965358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1965359 (x : real) (y : real) : (term93 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1965358) (@lem1965357 x y)). Qed.
Lemma lem1965361 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1965362 (x : real) (z : real) : (term92 x z) = (x = z).
Proof. exact (@lem1965361 (x = z)). Qed.
Lemma lem1965363 (y : real) (x : real) (z : real) : (term90 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1965359 x y) (@lem1965362 x z)). Qed.
Lemma lem1965364 (y : real) (x : real) (z : real) : (term89 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1965354 y x z) (@lem1965363 y x z)). Qed.
Lemma lem1965365 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1965366 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1965365) (@lem1965364 y x z)). Qed.
Lemma lem1965367 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1965368 (x : real) (y : real) (z : real) : (term85 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1965366 y x z) (@lem1965367 y z)). Qed.
Lemma lem1965369 (x : real) (y : real) (z : real) : (term81 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1965351 x y z) (@lem1965368 x y z)). Qed.
Lemma lem1965371 (h1 : term51) : term99.
Proof. exact (conj (@lem1965250 h1) (@lem1965258)). Qed.
Lemma lem1965373 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1965369 x y z) (@lem1965348 y x z)). Qed.
Lemma lem1965374 : term100.
Proof. exact (@lem1965373 term70 term65 term70). Qed.
Lemma lem1965377 (h1 : term51) : term65 = term70.
Proof. exact (@lem1965374 (@lem1965371 h1)). Qed.
Lemma lem1965378 (h1 : term51) : term101.
Proof. exact (fun h0 : term102 => @lem1965377 h1). Qed.
Lemma lem1965380 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965381 : term101 = (term65 = term70).
Proof. exact (@lem1965380 (term65 = term70)). Qed.
Lemma lem1965382 (h1 : term51) : term65 = term70.
Proof. exact (EQ_MP (@lem1965381) (@lem1965378 h1)). Qed.
Lemma lem1965383 (h1 : term51) (h2 : term54) : term103.
Proof. exact (conj (@lem1965242 h2) (@lem1965382 h1)). Qed.
Lemma lem1965385 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1965369 x y z) (@lem1965348 y x z)). Qed.
Lemma lem1965386 : term104.
Proof. exact (@lem1965385 term65 term11 term70). Qed.
Lemma lem1965389 (h1 : term51) (h2 : term54) : term11 = term70.
Proof. exact (@lem1965386 (@lem1965383 h1 h2)). Qed.
Lemma lem1965390 (h1 : term51) (h2 : term54) : term105.
Proof. exact (fun h0 : term106 => @lem1965389 h1 h2). Qed.
Lemma lem1965392 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965393 : term105 = (term11 = term70).
Proof. exact (@lem1965392 (term11 = term70)). Qed.
Lemma lem1965394 (h1 : term51) (h2 : term54) : term11 = term70.
Proof. exact (EQ_MP (@lem1965393) (@lem1965390 h1 h2)). Qed.
Lemma lem1965396 (h1 : term31 = term11) : term31 = term11.
Proof. exact (h1). Qed.
Lemma lem1965397 (h1 : term31 = term11) : term107.
Proof. exact (fun h0 : term30 => @lem1965396 h1). Qed.
Lemma lem1965399 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965400 : term107 = (term31 = term11).
Proof. exact (@lem1965399 (term31 = term11)). Qed.
Lemma lem1965401 (h1 : term31 = term11) : term31 = term11.
Proof. exact (EQ_MP (@lem1965400) (@lem1965397 h1)). Qed.
Lemma lem1965403 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1965404 : term31 = term31.
Proof. exact (@lem1965403 term31). Qed.
Lemma lem1965405 : term108.
Proof. exact (fun h0 : term109 => @lem1965404). Qed.
Lemma lem1965407 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965408 : term108 = (term31 = term31).
Proof. exact (@lem1965407 (term31 = term31)). Qed.
Lemma lem1965409 : term31 = term31.
Proof. exact (EQ_MP (@lem1965408) (@lem1965405)). Qed.
Lemma lem1965410 (h1 : term31 = term11) : term110.
Proof. exact (conj (@lem1965401 h1) (@lem1965409)). Qed.
Lemma lem1965412 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1965369 x y z) (@lem1965348 y x z)). Qed.
Lemma lem1965413 : term111.
Proof. exact (@lem1965412 term31 term11 term31). Qed.
Lemma lem1965416 (h1 : term31 = term11) : term11 = term31.
Proof. exact (@lem1965413 (@lem1965410 h1)). Qed.
Lemma lem1965417 (h1 : term31 = term11) : term112.
Proof. exact (fun h0 : term113 => @lem1965416 h1). Qed.
Lemma lem1965419 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965420 : term112 = (term11 = term31).
Proof. exact (@lem1965419 (term11 = term31)). Qed.
Lemma lem1965421 (h1 : term31 = term11) : term11 = term31.
Proof. exact (EQ_MP (@lem1965420) (@lem1965417 h1)). Qed.
Lemma lem1965422 (h1 : term51) (h2 : term54) (h3 : term31 = term11) : term114.
Proof. exact (conj (@lem1965394 h1 h2) (@lem1965421 h3)). Qed.
Lemma lem1965424 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1965369 x y z) (@lem1965348 y x z)). Qed.
Lemma lem1965425 : term115.
Proof. exact (@lem1965424 term11 term70 term31). Qed.
Lemma lem1965428 (h1 : term51) (h2 : term54) (h3 : term31 = term11) : term70 = term31.
Proof. exact (@lem1965425 (@lem1965422 h1 h2 h3)). Qed.
Lemma lem1965429 (h1 : term51) (h2 : term54) (h3 : term31 = term11) : term116.
Proof. exact (fun h0 : term61 => @lem1965428 h1 h2 h3). Qed.
Lemma lem1965431 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965432 : term116 = (term70 = term31).
Proof. exact (@lem1965431 (term70 = term31)). Qed.
Lemma lem1965433 (h1 : term51) (h2 : term54) (h3 : term31 = term11) : term70 = term31.
Proof. exact (EQ_MP (@lem1965432) (@lem1965429 h1 h2 h3)). Qed.
Lemma lem1965436 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1965438 : term61 = term117.
Proof. exact (@lem1965436 (term70 = term31)). Qed.
Lemma lem1965441 (x : real) (h1 : term24 x) (h2 : term11 = x) : term117.
Proof. exact (EQ_MP (@lem1965438) (@lem1965126 x h1 h2)). Qed.
Lemma lem1965444 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (@lem1965441 x h3 h4 (@lem1965433 h1 h2 h5)). Qed.
Lemma lem1965445 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term118.
Proof. exact (fun h0 : ~ False => @lem1965444 x h1 h2 h3 h4 h5). Qed.
Lemma lem1965447 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1965448 : term118 = False.
Proof. exact (@lem1965447 False). Qed.
Lemma lem1965449 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965448) (@lem1965445 x h1 h2 h3 h4 h5)). Qed.
Lemma lem1965450 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term31 = term11) = False.
Proof. exact (prop_ext (fun h6 : term31 = term11 => @lem1965449 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965168 h5)). Qed.
Lemma lem1965452 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965450 x h1 h2 h3 h4 h5) (@lem1965168 h5)). Qed.
Lemma lem1965453 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term31 = term11) = False.
Proof. exact (prop_ext (fun h6 : term31 = term11 => @lem1965452 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965098 h5)). Qed.
Lemma lem1965454 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965453 x h1 h2 h3 h4 h5) (@lem1965098 h5)). Qed.
Lemma lem1965455 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term24 x) = False.
Proof. exact (prop_ext (fun h6 : term24 x => @lem1965454 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965092 x h3)). Qed.
Lemma lem1965456 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965455 x h1 h2 h3 h4 h5) (@lem1965092 x h3)). Qed.
Lemma lem1965457 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term11 = x) = False.
Proof. exact (prop_ext (fun h6 : term11 = x => @lem1965456 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965090 x h4)). Qed.
Lemma lem1965458 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965457 x h1 h2 h3 h4 h5) (@lem1965090 x h4)). Qed.
Lemma lem1965459 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term31 = term11) = False.
Proof. exact (prop_ext (fun h6 : term31 = term11 => @lem1965458 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965079 h5)). Qed.
Lemma lem1965460 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965459 x h1 h2 h3 h4 h5) (@lem1965079 h5)). Qed.
Lemma lem1965461 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term24 x) = False.
Proof. exact (prop_ext (fun h6 : term24 x => @lem1965460 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965058 x h3)). Qed.
Lemma lem1965462 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965461 x h1 h2 h3 h4 h5) (@lem1965058 x h3)). Qed.
Lemma lem1965463 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term11 = x) = False.
Proof. exact (prop_ext (fun h6 : term11 = x => @lem1965462 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965054 x h4)). Qed.
Lemma lem1965464 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965463 x h1 h2 h3 h4 h5) (@lem1965054 x h4)). Qed.
Lemma lem1965465 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term31 = term11) = False.
Proof. exact (prop_ext (fun h6 : term31 = term11 => @lem1965464 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965079 h5)). Qed.
Lemma lem1965466 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965465 x h1 h2 h3 h4 h5) (@lem1965079 h5)). Qed.
Lemma lem1965467 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term51 = False.
Proof. exact (prop_ext (fun h6 : term51 => @lem1965466 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965075 h1)). Qed.
Lemma lem1965468 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965467 x h1 h2 h3 h4 h5) (@lem1965075 h1)). Qed.
Lemma lem1965469 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term54 = False.
Proof. exact (prop_ext (fun h6 : term54 => @lem1965468 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965065 h2)). Qed.
Lemma lem1965470 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965469 x h1 h2 h3 h4 h5) (@lem1965065 h2)). Qed.
Lemma lem1965471 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term24 x) = False.
Proof. exact (prop_ext (fun h6 : term24 x => @lem1965470 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965058 x h3)). Qed.
Lemma lem1965472 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965471 x h1 h2 h3 h4 h5) (@lem1965058 x h3)). Qed.
Lemma lem1965473 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term11 = x) = False.
Proof. exact (prop_ext (fun h6 : term11 = x => @lem1965472 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965054 x h4)). Qed.
Lemma lem1965474 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965473 x h1 h2 h3 h4 h5) (@lem1965054 x h4)). Qed.
Lemma lem1965475 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term31 = term11) = False.
Proof. exact (prop_ext (fun h6 : term31 = term11 => @lem1965474 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965050 h5)). Qed.
Lemma lem1965476 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965475 x h1 h2 h3 h4 h5) (@lem1965050 h5)). Qed.
Lemma lem1965477 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term51 = False.
Proof. exact (prop_ext (fun h6 : term51 => @lem1965476 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965034 h1)). Qed.
Lemma lem1965478 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965477 x h1 h2 h3 h4 h5) (@lem1965034 h1)). Qed.
Lemma lem1965479 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term54 = False.
Proof. exact (prop_ext (fun h6 : term54 => @lem1965478 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1965012 h2)). Qed.
Lemma lem1965480 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965479 x h1 h2 h3 h4 h5) (@lem1965012 h2)). Qed.
Lemma lem1965481 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term24 x) = False.
Proof. exact (prop_ext (fun h6 : term24 x => @lem1965480 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964991 x h3)). Qed.
Lemma lem1965482 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965481 x h1 h2 h3 h4 h5) (@lem1964991 x h3)). Qed.
Lemma lem1965483 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term11 = x) = False.
Proof. exact (prop_ext (fun h6 : term11 = x => @lem1965482 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964975 x h4)). Qed.
Lemma lem1965484 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965483 x h1 h2 h3 h4 h5) (@lem1964975 x h4)). Qed.
Lemma lem1965485 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term31 = term11) = False.
Proof. exact (prop_ext (fun h6 : term31 = term11 => @lem1965484 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964965 h5)). Qed.
Lemma lem1965486 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965485 x h1 h2 h3 h4 h5) (@lem1964965 h5)). Qed.
Lemma lem1965487 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term51 = False.
Proof. exact (prop_ext (fun h6 : term51 => @lem1965486 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964959 h1)). Qed.
Lemma lem1965488 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965487 x h1 h2 h3 h4 h5) (@lem1964959 h1)). Qed.
Lemma lem1965489 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : term54 = False.
Proof. exact (prop_ext (fun h6 : term54 => @lem1965488 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964939 h2)). Qed.
Lemma lem1965490 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965489 x h1 h2 h3 h4 h5) (@lem1964939 h2)). Qed.
Lemma lem1965491 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term24 x) = False.
Proof. exact (prop_ext (fun h6 : term24 x => @lem1965490 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964926 x h3)). Qed.
Lemma lem1965492 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965491 x h1 h2 h3 h4 h5) (@lem1964926 x h3)). Qed.
Lemma lem1965493 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : (term11 = x) = False.
Proof. exact (prop_ext (fun h6 : term11 = x => @lem1965492 x h1 h2 h3 h4 h5) (fun h6 : False => @lem1964920 x h4)). Qed.
Lemma lem1965494 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) (h5 : term31 = term11) : False.
Proof. exact (EQ_MP (@lem1965493 x h1 h2 h3 h4 h5) (@lem1964920 x h4)). Qed.
Lemma lem1965495 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) : term29.
Proof. exact (fun h0 : term31 = term11 => @lem1965494 x h1 h2 h3 h4 h0). Qed.
Lemma lem1965496 : term29 = term30.
Proof. exact (@lem69 (term31 = term11)). Qed.
Lemma lem1965497 (x : real) (h1 : term51) (h2 : term54) (h3 : term24 x) (h4 : term11 = x) : term30.
Proof. exact (EQ_MP (@lem1965496) (@lem1965495 x h1 h2 h3 h4)). Qed.
Lemma lem1965498 (x : real) (h1 : term54) (h2 : term24 x) (h3 : term11 = x) : term34.
Proof. exact (fun h0 : term51 => @lem1965497 x h0 h1 h2 h3). Qed.
Lemma lem1965499 (x : real) (h1 : term24 x) (h2 : term11 = x) : term37.
Proof. exact (fun h0 : term54 => @lem1965498 x h0 h1 h2). Qed.
Lemma lem1965500 (x : real) (h1 : term11 = x) : term40 x.
Proof. exact (fun h0 : term24 x => @lem1965499 x h0 h1). Qed.
Lemma lem1965501 (x : real) : term42 x.
Proof. exact (fun h0 : term11 = x => @lem1965500 x h0). Qed.
Lemma lem1965506 : term46.
Proof. exact (fun x : real => @lem1965501 x). Qed.
Lemma lem1965507 : term45.
Proof. exact (EQ_MP (@lem1964909) (@lem1965506)). Qed.
Lemma lem1965508 (x : real) : term119 x.
Proof. exact (@lem1965507 x). Qed.
Lemma lem1965509 (x : real) : (term119 x) = (term25 x).
Proof. exact (eq_refl (term119 x)). Qed.
Lemma lem1965510 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1965509 x) (@lem1965508 x)). Qed.
Lemma lem1965512 (x : real) : term25 x.
Proof. exact (@lem1964786 x (@lem1965510 x)). Qed.
Lemma lem1965513 (x : real) (h1 : term11 = x) : term39 x.
Proof. exact (@lem1965512 x (@lem1964766 x h1)). Qed.
Lemma lem1965514 (x : real) (h1 : term24 x) (h2 : term11 = x) : term36.
Proof. exact (@lem1965513 x h2 (@lem1964771 x h1)). Qed.
Lemma lem1965515 (x : real) (h1 : term24 x) (h2 : term11 = x) : term33.
Proof. exact (@lem1965514 x h1 h2 (@lem1357243)). Qed.
Lemma lem1965516 (x : real) (h1 : term24 x) (h2 : term11 = x) : term29.
Proof. exact (@lem1965515 x h1 h2 (@lem1344936)). Qed.
Lemma lem1965517 (x : real) (h1 : term24 x) (h2 : term11 = x) : False.
Proof. exact (@lem1965516 x h1 h2 (@lem1901741)). Qed.
Lemma lem1965518 (x : real) (h1 : term24 x) (h2 : term11 = x) : (term24 x) = False.
Proof. exact (prop_ext (fun h3 : term24 x => @lem1965517 x h1 h2) (fun h3 : False => @lem1964771 x h1)). Qed.
Lemma lem1965519 (x : real) (h1 : term24 x) (h2 : term11 = x) : False.
Proof. exact (EQ_MP (@lem1965518 x h1 h2) (@lem1964771 x h1)). Qed.
Lemma lem1965520 (x : real) (h1 : term11 = x) : term23 x.
Proof. exact (fun h0 : term24 x => @lem1965519 x h0 h1). Qed.
Lemma lem1965521 (x : real) (h1 : term11 = x) : (term14 x) = (sqrt x).
Proof. exact (EQ_MP (@lem1964770 x) (@lem1965520 x h1)). Qed.
Lemma lem1965522 (x : real) : term120 x.
Proof. exact (@lem1964718 x). Qed.
Lemma lem1965523 (x : real) : (term120 x) = ((real_mul x x) = (term0 x)).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1965525 (x : real) : term121 x.
Proof. exact (@lem1957847 x). Qed.
Lemma lem1965526 (x : real) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1965527 (x : real) : term122 x.
Proof. exact (EQ_MP (@lem1965526 x) (@lem1965525 x)). Qed.
Lemma lem1965528 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (h1). Qed.
Lemma lem1965529 (x : real) (h1 : term21 x) : term123 x.
Proof. exact (@lem1965527 x (@lem1965528 x h1)). Qed.
Lemma lem1965530 (x : real) : (term123 x) = ((term123 x) = True).
Proof. exact (@lem7 (term123 x)). Qed.
Lemma lem1965531 (x : real) (h1 : term21 x) : (term123 x) = True.
Proof. exact (EQ_MP (@lem1965530 x) (@lem1965529 x h1)). Qed.
Lemma lem1965537 (x : real) : term124 x.
Proof. exact (@lem1629489 x). Qed.
Lemma lem1965538 (x : real) : (term124 x) = (term125 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1965539 (x : real) : term125 x.
Proof. exact (EQ_MP (@lem1965538 x) (@lem1965537 x)). Qed.
Lemma lem1965540 (x : real) (y : real) : term126 x y.
Proof. exact (@lem1965539 x y). Qed.
Lemma lem1965541 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem1965542 (x : real) (y : real) : term127 x y.
Proof. exact (EQ_MP (@lem1965541 x y) (@lem1965540 x y)). Qed.
Lemma lem1965543 (x : real) (y : real) (z : real) : term128 x y z.
Proof. exact (@lem1965542 x y z). Qed.
Lemma lem1965544 (x : real) (y : real) (z : real) : (term128 x y z) = (term129 x y z).
Proof. exact (eq_refl (term128 x y z)). Qed.
Lemma lem1965545 (x : real) (y : real) (z : real) : term129 x y z.
Proof. exact (EQ_MP (@lem1965544 x y z) (@lem1965543 x y z)). Qed.
Lemma lem1965546 (z : real) (h1 : term21 z) : term21 z.
Proof. exact (h1). Qed.
Lemma lem1965547 (x : real) (y : real) (z : real) (h1 : term21 z) : ((real_div x z) = y) = (x = (real_mul y z)).
Proof. exact (@lem1965545 x y z (@lem1965546 z h1)). Qed.
Lemma lem1965553 (x : real) : (term21 x) = ((term21 x) = True).
Proof. exact (@lem7 (term21 x)). Qed.
Lemma lem1965556 (x : real) (y : real) (z : real) : term129 x y z.
Proof. exact (fun h0 : term21 z => @lem1965547 x y z h0). Qed.
Lemma lem1965557 (x : real) : term130 x.
Proof. exact (@lem1965556 x (sqrt x) (sqrt x)). Qed.
Lemma lem1965559 (x : real) : term131 x.
Proof. exact (fun h0 : term21 x => @lem1965531 x h0). Qed.
Lemma lem1965561 (x : real) (h1 : term21 x) : (term21 x) = True.
Proof. exact (EQ_MP (@lem1965553 x) (@lem1964765 x h1)). Qed.
Lemma lem1965562 (x : real) (h1 : term21 x) : True = (term21 x).
Proof. exact (SYM (@lem1965561 x h1)). Qed.
Lemma lem1965563 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (EQ_MP (@lem1965562 x h1) (@lem0)). Qed.
Lemma lem1965564 (x : real) (h1 : term21 x) : (term123 x) = True.
Proof. exact (@lem1965559 x (@lem1965563 x h1)). Qed.
Lemma lem1965565 (x : real) (h1 : term21 x) : True = (term123 x).
Proof. exact (SYM (@lem1965564 x h1)). Qed.
Lemma lem1965566 (x : real) (h1 : term21 x) : term123 x.
Proof. exact (EQ_MP (@lem1965565 x h1) (@lem0)). Qed.
Lemma lem1965567 (x : real) (h1 : term21 x) : ((term14 x) = (sqrt x)) = (x = (term132 x)).
Proof. exact (@lem1965557 x (@lem1965566 x h1)). Qed.
Lemma lem1965571 (x : real) : (real_mul x x) = (term0 x).
Proof. exact (EQ_MP (@lem1965523 x) (@lem1965522 x)). Qed.
Lemma lem1965572 (x : real) : (term132 x) = (term133 x).
Proof. exact (@lem1965571 (sqrt x)). Qed.
Lemma lem1965573 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem1965574 (x : real) : (x = (term132 x)) = (x = (term133 x)).
Proof. exact (MK_COMB (@lem1965573 x) (@lem1965572 x)). Qed.
Lemma lem1965577 (x : real) (h1 : term21 x) : ((term14 x) = (sqrt x)) = (x = (term133 x)).
Proof. exact (TRANS (@lem1965567 x h1) (@lem1965574 x)). Qed.
Lemma lem1965578 (x : real) (h1 : term21 x) : (x = (term133 x)) = ((term14 x) = (sqrt x)).
Proof. exact (SYM (@lem1965577 x h1)). Qed.
Lemma lem1965579 (x : real) : term134 x.
Proof. exact (@lem1369133 x). Qed.
Lemma lem1965580 (x : real) : (term134 x) = (term135 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1965581 (x : real) : term135 x.
Proof. exact (EQ_MP (@lem1965580 x) (@lem1965579 x)). Qed.
Lemma lem1965582 (x : real) (y : real) : term136 x y.
Proof. exact (@lem1965581 x y). Qed.
Lemma lem1965583 (x : real) (y : real) : (term136 x y) = (term137 x y).
Proof. exact (eq_refl (term136 x y)). Qed.
Lemma lem1965584 (x : real) (y : real) : term137 x y.
Proof. exact (EQ_MP (@lem1965583 x y) (@lem1965582 x y)). Qed.
Lemma lem1965585 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1965586 (x : real) (y : real) (h1 : real_lt x y) : real_le x y.
Proof. exact (@lem1965584 x y (@lem1965585 x y h1)). Qed.
Lemma lem1965587 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1965588 (x : real) (y : real) (h1 : real_lt x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1965587 x y) (@lem1965586 x y h1)). Qed.
Lemma lem1965594 (x : real) : term138 x.
Proof. exact (@lem1945848 x). Qed.
Lemma lem1965595 (x : real) : (term138 x) = (term139 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1965596 (x : real) : term139 x.
Proof. exact (EQ_MP (@lem1965595 x) (@lem1965594 x)). Qed.
Lemma lem1965597 (x : real) (h1 : term9 x) : term9 x.
Proof. exact (h1). Qed.
Lemma lem1965598 (x : real) (h1 : term9 x) : (term133 x) = x.
Proof. exact (@lem1965596 x (@lem1965597 x h1)). Qed.
Lemma lem1965604 (x : real) : (term21 x) = ((term21 x) = True).
Proof. exact (@lem7 (term21 x)). Qed.
Lemma lem1965609 (x : real) : term139 x.
Proof. exact (fun h0 : term9 x => @lem1965598 x h0). Qed.
Lemma lem1965611 (x : real) (y : real) : term140 x y.
Proof. exact (fun h0 : real_lt x y => @lem1965588 x y h0). Qed.
Lemma lem1965612 (x : real) : term141 x.
Proof. exact (@lem1965611 term11 x). Qed.
Lemma lem1965614 (x : real) (h1 : term21 x) : (term21 x) = True.
Proof. exact (EQ_MP (@lem1965604 x) (@lem1964765 x h1)). Qed.
Lemma lem1965615 (x : real) (h1 : term21 x) : True = (term21 x).
Proof. exact (SYM (@lem1965614 x h1)). Qed.
Lemma lem1965616 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (EQ_MP (@lem1965615 x h1) (@lem0)). Qed.
Lemma lem1965617 (x : real) (h1 : term21 x) : (term9 x) = True.
Proof. exact (@lem1965612 x (@lem1965616 x h1)). Qed.
Lemma lem1965618 (x : real) (h1 : term21 x) : True = (term9 x).
Proof. exact (SYM (@lem1965617 x h1)). Qed.
Lemma lem1965619 (x : real) (h1 : term21 x) : term9 x.
Proof. exact (EQ_MP (@lem1965618 x h1) (@lem0)). Qed.
Lemma lem1965620 (x : real) (h1 : term21 x) : (term133 x) = x.
Proof. exact (@lem1965609 x (@lem1965619 x h1)). Qed.
Lemma lem1965621 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem1965622 (x : real) (h1 : term21 x) : (x = (term133 x)) = (x = x).
Proof. exact (MK_COMB (@lem1965621 x) (@lem1965620 x h1)). Qed.
Lemma lem1965624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1965625 (x : real) : (x = x) = True.
Proof. exact (@lem1965624 real x). Qed.
Lemma lem1965626 (x : real) (h1 : term21 x) : (x = (term133 x)) = True.
Proof. exact (TRANS (@lem1965622 x h1) (@lem1965625 x)). Qed.
Lemma lem1965627 (x : real) (h1 : term21 x) : True = (x = (term133 x)).
Proof. exact (SYM (@lem1965626 x h1)). Qed.
Lemma lem1965628 (x : real) (h1 : term21 x) : x = (term133 x).
Proof. exact (EQ_MP (@lem1965627 x h1) (@lem0)). Qed.
Lemma lem1965629 (x : real) (h1 : term21 x) : (term14 x) = (sqrt x).
Proof. exact (EQ_MP (@lem1965578 x h1) (@lem1965628 x h1)). Qed.
Lemma lem1965630 (x : real) (h1 : term11 = x) : (term11 = x) = ((term14 x) = (sqrt x)).
Proof. exact (prop_ext (fun h2 : term11 = x => @lem1965521 x h1) (fun h2 : (term14 x) = (sqrt x) => @lem1964766 x h1)). Qed.
Lemma lem1965631 (x : real) (h1 : term11 = x) : (term14 x) = (sqrt x).
Proof. exact (EQ_MP (@lem1965630 x h1) (@lem1964766 x h1)). Qed.
Lemma lem1965632 (x : real) (h1 : term21 x) : (term21 x) = ((term14 x) = (sqrt x)).
Proof. exact (prop_ext (fun h2 : term21 x => @lem1965629 x h1) (fun h2 : (term14 x) = (sqrt x) => @lem1964765 x h1)). Qed.
Lemma lem1965633 (x : real) (h1 : term21 x) : (term14 x) = (sqrt x).
Proof. exact (EQ_MP (@lem1965632 x h1) (@lem1964765 x h1)). Qed.
Lemma lem1965634 (x : real) (h1 : term10 x) : (term14 x) = (sqrt x).
Proof. exact (or_elim (@lem1964764 x h1) (fun h0 : term21 x => @lem1965633 x h0) (fun h0 : term11 = x => @lem1965631 x h0)). Qed.
Lemma lem1965635 (x : real) : term16 x.
Proof. exact (fun h0 : term10 x => @lem1965634 x h0). Qed.
Lemma lem1965640 : term20.
Proof. exact (fun x : real => @lem1965635 x). Qed.
Lemma lem1965641 : term19.
Proof. exact (EQ_MP (@lem1964763) (@lem1965640)). Qed.
