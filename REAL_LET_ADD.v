Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LET_ADD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LTE_ADD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1380654 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1380655 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1380656 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1380655 t1) (@lem1380654 t1)). Qed.
Lemma lem1380657 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1380656 t1 t2). Qed.
Lemma lem1380658 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1380659 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1380658 t1 t2) (@lem1380657 t1 t2)). Qed.
Lemma lem1380660 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1380659 t1 t2 t3). Qed.
Lemma lem1380661 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1380662 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1380661 t1 t2 t3) (@lem1380660 t1 t2 t3)). Qed.
Lemma lem1380663 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1380662 t1 t2 t3)). Qed.
Lemma lem1380665 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1380666 : term8 = term9.
Proof. exact (@lem1380665 term8). Qed.
Lemma lem1380667 : term9 = term8.
Proof. exact (SYM (@lem1380666)). Qed.
Lemma lem1380668 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1380671 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1380672 : term12.
Proof. exact (fun h0 : term11 => @lem1380671 h0). Qed.
Lemma lem1380673 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1380674 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1380675 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1380673 h2 (@lem1380674 h1)). Qed.
Lemma lem1380676 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1380675 h1 h0). Qed.
Lemma lem1380677 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1380678 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1380676 h1 (@lem1380677 h2)). Qed.
Lemma lem1380679 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1380678 h0 h1). Qed.
Lemma lem1380680 : term14.
Proof. exact (fun h0 : term12 => @lem1380679 h0). Qed.
Lemma lem1380683 : term12.
Proof. exact (@lem1380680 (@lem1380672)). Qed.
Lemma lem1380709 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1380710 : term15 = term16.
Proof. exact (@lem1380709 term17). Qed.
Lemma lem1380723 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1380724 : term19 = term20.
Proof. exact (MK_COMB (@lem1380723) (@lem1380710)). Qed.
Lemma lem1380727 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1380734 : term11 = term22.
Proof. exact (MK_COMB (@lem1380727) (@lem1380724)). Qed.
Lemma lem1380743 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1380744 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : real => @lem1380743 x y)). Qed.
Lemma lem1380745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380746 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1380745) (@lem1380744 x)). Qed.
Lemma lem1380747 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1380746 x)). Qed.
Lemma lem1380748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380749 : term17 = term17.
Proof. exact (MK_COMB (@lem1380748) (@lem1380747)). Qed.
Lemma lem1380750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1380751 : term16 = term16.
Proof. exact (MK_COMB (@lem1380750) (@lem1380749)). Qed.
Lemma lem1380752 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1380753 (x : real) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1380752 y x)). Qed.
Lemma lem1380754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380755 (x : real) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem1380754) (@lem1380753 x)). Qed.
Lemma lem1380756 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1380755 x)). Qed.
Lemma lem1380757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380758 : term30 = term30.
Proof. exact (MK_COMB (@lem1380757) (@lem1380756)). Qed.
Lemma lem1380759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1380760 : term18 = term18.
Proof. exact (MK_COMB (@lem1380759) (@lem1380758)). Qed.
Lemma lem1380761 : term20 = term20.
Proof. exact (MK_COMB (@lem1380760) (@lem1380751)). Qed.
Lemma lem1380770 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1380771 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1380770 x y)). Qed.
Lemma lem1380772 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380773 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1380772) (@lem1380771 x)). Qed.
Lemma lem1380774 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1380773 x)). Qed.
Lemma lem1380775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380776 : term8 = term8.
Proof. exact (MK_COMB (@lem1380775) (@lem1380774)). Qed.
Lemma lem1380777 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1380778 : term10 = term10.
Proof. exact (MK_COMB (@lem1380777) (@lem1380776)). Qed.
Lemma lem1380779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1380780 : term21 = term21.
Proof. exact (MK_COMB (@lem1380779) (@lem1380778)). Qed.
Lemma lem1380781 : term22 = term22.
Proof. exact (MK_COMB (@lem1380780) (@lem1380761)). Qed.
Lemma lem1380832 : term11 = term22.
Proof. exact (TRANS (@lem1380734) (@lem1380781)). Qed.
Lemma lem1380833 : term22 = term11.
Proof. exact (SYM (@lem1380832)). Qed.
Lemma lem1380834 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1380835 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1380836 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1380847 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem17362 (term37 x y) (term38 x y)). Qed.
Lemma lem1380848 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1380849 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1380848 (term32 x)). Qed.
Lemma lem1380850 (x : real) (y : real) : (term43 x y) = (term31 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1380851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1380852 (x : real) (y : real) : (term44 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1380851) (@lem1380850 x y)). Qed.
Lemma lem1380853 (x : real) (y : real) : (term44 x y) = (term36 x y).
Proof. exact (TRANS (@lem1380852 x y) (@lem1380847 x y)). Qed.
Lemma lem1380854 (x : real) : (term45 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1380853 x y)). Qed.
Lemma lem1380855 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1380856 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1380855) (@lem1380854 x)). Qed.
Lemma lem1380857 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1380849 x) (@lem1380856 x)). Qed.
Lemma lem1380858 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1380859 : term10 = term48.
Proof. exact (@lem1380858 term34). Qed.
Lemma lem1380860 (x : real) : (term49 x) = (term33 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1380861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1380862 (x : real) : (term50 x) = (term41 x).
Proof. exact (MK_COMB (@lem1380861) (@lem1380860 x)). Qed.
Lemma lem1380863 (x : real) : (term50 x) = (term47 x).
Proof. exact (TRANS (@lem1380862 x) (@lem1380857 x)). Qed.
Lemma lem1380864 : term51 = term52.
Proof. exact (fun_ext (fun x : real => @lem1380863 x)). Qed.
Lemma lem1380865 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1380866 : term48 = term53.
Proof. exact (MK_COMB (@lem1380865) (@lem1380864)). Qed.
Lemma lem1380923 : term10 = term53.
Proof. exact (TRANS (@lem1380859) (@lem1380866)). Qed.
Lemma lem1380924 (h1 : term10) : term53.
Proof. exact (EQ_MP (@lem1380923) (@lem1380834 h1)). Qed.
Lemma lem1380925 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1380926 (x : real) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1380925 y x)). Qed.
Lemma lem1380927 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380928 (x : real) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem1380927) (@lem1380926 x)). Qed.
Lemma lem1380929 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1380928 x)). Qed.
Lemma lem1380930 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380943 : term30 = term30.
Proof. exact (MK_COMB (@lem1380930) (@lem1380929)). Qed.
Lemma lem1380944 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1380943) (@lem1380835 h1)). Qed.
Lemma lem1380951 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (@lem17045 (term56 x) (term57 y)). Qed.
Lemma lem1380952 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1380953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1380954 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1380953) (@lem1380951 x y)). Qed.
Lemma lem1380955 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1380954 x y) (@lem1380952 x y)). Qed.
Lemma lem1380956 (x : real) (y : real) : (term23 x y) = (term60 x y).
Proof. exact (@lem17265 (term62 x y) (term38 x y)). Qed.
Lemma lem1380957 (x : real) (y : real) : (term23 x y) = (term61 x y).
Proof. exact (TRANS (@lem1380956 x y) (@lem1380955 x y)). Qed.
Lemma lem1380958 (x : real) : (term24 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1380957 x y)). Qed.
Lemma lem1380959 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380960 (x : real) : (term25 x) = (term64 x).
Proof. exact (MK_COMB (@lem1380959) (@lem1380958 x)). Qed.
Lemma lem1380961 : term26 = term65.
Proof. exact (fun_ext (fun x : real => @lem1380960 x)). Qed.
Lemma lem1380962 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381019 : term17 = term66.
Proof. exact (MK_COMB (@lem1380962) (@lem1380961)). Qed.
Lemma lem1381020 (h1 : term17) : term66.
Proof. exact (EQ_MP (@lem1381019) (@lem1380836 h1)). Qed.
Lemma lem1381021 (x : real) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1381035 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1381036 (x : real) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1381035 y x)). Qed.
Lemma lem1381037 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381038 (x : real) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem1381037) (@lem1381036 x)). Qed.
Lemma lem1381039 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1381038 x)). Qed.
Lemma lem1381040 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381041 : term30 = term30.
Proof. exact (MK_COMB (@lem1381040) (@lem1381039)). Qed.
Lemma lem1381042 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1381041) (@lem1380944 h1)). Qed.
Lemma lem1381083 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1381084 (x : real) : (term63 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1381083 x y)). Qed.
Lemma lem1381085 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381086 (x : real) : (term64 x) = (term64 x).
Proof. exact (MK_COMB (@lem1381085) (@lem1381084 x)). Qed.
Lemma lem1381087 : term65 = term65.
Proof. exact (fun_ext (fun x : real => @lem1381086 x)). Qed.
Lemma lem1381088 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381089 : term66 = term66.
Proof. exact (MK_COMB (@lem1381088) (@lem1381087)). Qed.
Lemma lem1381090 (h1 : term17) : term66.
Proof. exact (EQ_MP (@lem1381089) (@lem1381020 h1)). Qed.
Lemma lem1381130 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1381132 (x : real) (y : real) (h1 : term36 x y) : term37 x y.
Proof. exact (proj1 (@lem1381130 x y h1)). Qed.
Lemma lem1381136 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1381137 (x : real) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1381136 y x)). Qed.
Lemma lem1381138 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381139 (x : real) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem1381138) (@lem1381137 x)). Qed.
Lemma lem1381140 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1381139 x)). Qed.
Lemma lem1381141 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381143 : term30 = term30.
Proof. exact (MK_COMB (@lem1381141) (@lem1381140)). Qed.
Lemma lem1381144 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1381143) (@lem1381042 h1)). Qed.
Lemma lem1381158 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1381159 (x : real) : (term63 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1381158 x y)). Qed.
Lemma lem1381160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381161 (x : real) : (term64 x) = (term64 x).
Proof. exact (MK_COMB (@lem1381160) (@lem1381159 x)). Qed.
Lemma lem1381162 : term65 = term65.
Proof. exact (fun_ext (fun x : real => @lem1381161 x)). Qed.
Lemma lem1381163 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1381165 : term66 = term66.
Proof. exact (MK_COMB (@lem1381163) (@lem1381162)). Qed.
Lemma lem1381166 (h1 : term17) : term66.
Proof. exact (EQ_MP (@lem1381165) (@lem1381090 h1)). Qed.
Lemma lem1381179 (_24471 : real) (h1 : term30) : term67 _24471.
Proof. exact (@lem1381144 h1 _24471). Qed.
Lemma lem1381180 (_24471 : real) : (term67 _24471) = (term28 _24471).
Proof. exact (eq_refl (term67 _24471)). Qed.
Lemma lem1381181 (_24471 : real) (h1 : term30) : term28 _24471.
Proof. exact (EQ_MP (@lem1381180 _24471) (@lem1381179 _24471 h1)). Qed.
Lemma lem1381182 (_24471 : real) (_24472 : real) (h1 : term30) : term68 _24471 _24472.
Proof. exact (@lem1381181 _24471 h1 _24472). Qed.
Lemma lem1381183 (_24472 : real) (_24471 : real) : (term68 _24471 _24472) = ((real_add _24471 _24472) = (real_add _24472 _24471)).
Proof. exact (eq_refl (term68 _24471 _24472)). Qed.
Lemma lem1381185 (_24473 : real) (h1 : term17) : term69 _24473.
Proof. exact (@lem1381166 h1 _24473). Qed.
Lemma lem1381186 (_24473 : real) : (term69 _24473) = (term64 _24473).
Proof. exact (eq_refl (term69 _24473)). Qed.
Lemma lem1381187 (_24473 : real) (h1 : term17) : term64 _24473.
Proof. exact (EQ_MP (@lem1381186 _24473) (@lem1381185 _24473 h1)). Qed.
Lemma lem1381188 (_24473 : real) (_24474 : real) (h1 : term17) : term70 _24473 _24474.
Proof. exact (@lem1381187 _24473 h1 _24474). Qed.
Lemma lem1381189 (_24473 : real) (_24474 : real) : (term70 _24473 _24474) = (term61 _24473 _24474).
Proof. exact (eq_refl (term70 _24473 _24474)). Qed.
Lemma lem1381190 (_24473 : real) (_24474 : real) (h1 : term17) : term61 _24473 _24474.
Proof. exact (EQ_MP (@lem1381189 _24473 _24474) (@lem1381188 _24473 _24474 h1)). Qed.
Lemma lem1381203 (_24473 : real) (_24474 : real) : (term61 _24473 _24474) = (term71 _24473 _24474).
Proof. exact (@lem1380663 (term72 _24473) (term73 _24474) (term38 _24473 _24474)). Qed.
Lemma lem1381204 (_24473 : real) (_24474 : real) (h1 : term17) : term71 _24473 _24474.
Proof. exact (EQ_MP (@lem1381203 _24473 _24474) (@lem1381190 _24473 _24474 h1)). Qed.
Lemma lem1381206 (x : real) (y : real) (h1 : term36 x y) : term74 x y.
Proof. exact (proj2 (@lem1381130 x y h1)). Qed.
Lemma lem1381230 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1381231 (_24479 : real) (_24481 : real) (h1 : _24479 = _24481) : _24479 = _24481.
Proof. exact (h1). Qed.
Lemma lem1381232 (_24480 : real) (_24482 : real) (h1 : _24480 = _24482) : _24480 = _24482.
Proof. exact (h1). Qed.
Lemma lem1381233 (_24479 : real) (_24481 : real) (h1 : _24479 = _24481) : (real_lt _24479) = (real_lt _24481).
Proof. exact (MK_COMB (@lem1381230) (@lem1381231 _24479 _24481 h1)). Qed.
Lemma lem1381234 (_24479 : real) (_24481 : real) (_24480 : real) (_24482 : real) (h1 : _24479 = _24481) (h2 : _24480 = _24482) : (real_lt _24479 _24480) = (real_lt _24481 _24482).
Proof. exact (MK_COMB (@lem1381233 _24479 _24481 h1) (@lem1381232 _24480 _24482 h2)). Qed.
Lemma lem1381236 (b : Prop) (a : Prop) : term75 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1381237 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : term76 _24481 _24482 _24479 _24480.
Proof. exact (@lem1381236 (real_lt _24481 _24482) (real_lt _24479 _24480)). Qed.
Lemma lem1381238 (_24479 : real) (_24481 : real) (_24480 : real) (_24482 : real) (h1 : _24479 = _24481) (h2 : _24480 = _24482) : term77 _24481 _24482 _24479 _24480.
Proof. exact (@lem1381237 _24481 _24482 _24479 _24480 (@lem1381234 _24479 _24481 _24480 _24482 h1 h2)). Qed.
Lemma lem1381239 (_24482 : real) (_24480 : real) (_24479 : real) (_24481 : real) (h1 : _24479 = _24481) : term78 _24481 _24482 _24479 _24480.
Proof. exact (fun h0 : _24480 = _24482 => @lem1381238 _24479 _24481 _24480 _24482 h1 h0). Qed.
Lemma lem1381241 (a : Prop) (b : Prop) : (a -> b) = (term79 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1381242 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term78 _24481 _24482 _24479 _24480) = (term80 _24481 _24482 _24479 _24480).
Proof. exact (@lem1381241 (_24480 = _24482) (term77 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381243 (_24482 : real) (_24480 : real) (_24479 : real) (_24481 : real) (h1 : _24479 = _24481) : term80 _24481 _24482 _24479 _24480.
Proof. exact (EQ_MP (@lem1381242 _24481 _24482 _24479 _24480) (@lem1381239 _24482 _24480 _24479 _24481 h1)). Qed.
Lemma lem1381244 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : term81 _24481 _24482 _24479 _24480.
Proof. exact (fun h0 : _24479 = _24481 => @lem1381243 _24482 _24480 _24479 _24481 h0). Qed.
Lemma lem1381246 (a : Prop) (b : Prop) : (a -> b) = (term79 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1381247 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term81 _24481 _24482 _24479 _24480) = (term82 _24481 _24482 _24479 _24480).
Proof. exact (@lem1381246 (_24479 = _24481) (term80 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381248 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : term82 _24481 _24482 _24479 _24480.
Proof. exact (EQ_MP (@lem1381247 _24481 _24482 _24479 _24480) (@lem1381244 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381285 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1381286 : term83 = term83.
Proof. exact (@lem1381285 term83). Qed.
Lemma lem1381287 : term84.
Proof. exact (fun h0 : term85 => @lem1381286). Qed.
Lemma lem1381289 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381290 : term84 = (term83 = term83).
Proof. exact (@lem1381289 (term83 = term83)). Qed.
Lemma lem1381291 : term83 = term83.
Proof. exact (EQ_MP (@lem1381290) (@lem1381287)). Qed.
Lemma lem1381293 (_24472 : real) (_24471 : real) (h1 : term30) : (real_add _24471 _24472) = (real_add _24472 _24471).
Proof. exact (EQ_MP (@lem1381183 _24472 _24471) (@lem1381182 _24471 _24472 h1)). Qed.
Lemma lem1381294 (x : real) (y : real) (h1 : term30) : (real_add y x) = (real_add x y).
Proof. exact (@lem1381293 x y h1). Qed.
Lemma lem1381295 (x : real) (y : real) (h1 : term30) : term87 x y.
Proof. exact (fun h0 : term88 x y => @lem1381294 x y h1). Qed.
Lemma lem1381297 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381298 (x : real) (y : real) : (term87 x y) = ((real_add y x) = (real_add x y)).
Proof. exact (@lem1381297 ((real_add y x) = (real_add x y))). Qed.
Lemma lem1381299 (x : real) (y : real) (h1 : term30) : (real_add y x) = (real_add x y).
Proof. exact (EQ_MP (@lem1381298 x y) (@lem1381295 x y h1)). Qed.
Lemma lem1381301 (x : real) (y : real) (h1 : term36 x y) : term56 y.
Proof. exact (proj2 (@lem1381132 x y h1)). Qed.
Lemma lem1381302 (x : real) (y : real) (h1 : term36 x y) : term89 y.
Proof. exact (fun h0 : term72 y => @lem1381301 x y h1). Qed.
Lemma lem1381304 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381305 (y : real) : (term89 y) = (term56 y).
Proof. exact (@lem1381304 (term56 y)). Qed.
Lemma lem1381306 (x : real) (y : real) (h1 : term36 x y) : term56 y.
Proof. exact (EQ_MP (@lem1381305 y) (@lem1381302 x y h1)). Qed.
Lemma lem1381308 (x : real) (y : real) (h1 : term36 x y) : term57 x.
Proof. exact (proj1 (@lem1381132 x y h1)). Qed.
Lemma lem1381309 (x : real) (y : real) (h1 : term36 x y) : term90 x.
Proof. exact (fun h0 : term73 x => @lem1381308 x y h1). Qed.
Lemma lem1381311 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381312 (x : real) : (term90 x) = (term57 x).
Proof. exact (@lem1381311 (term57 x)). Qed.
Lemma lem1381313 (x : real) (y : real) (h1 : term36 x y) : term57 x.
Proof. exact (EQ_MP (@lem1381312 x) (@lem1381309 x y h1)). Qed.
Lemma lem1381319 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1381320 (_24473 : real) (_24474 : real) : (term71 _24473 _24474) = (term91 _24473 _24474).
Proof. exact (@lem1381319 (term73 _24474) (term72 _24473) (term38 _24473 _24474)). Qed.
Lemma lem1381334 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1381335 (_24474 : real) (_24473 : real) : (term92 _24473 _24474) = (term93 _24474 _24473).
Proof. exact (@lem1381334 (term38 _24473 _24474) (term72 _24473)). Qed.
Lemma lem1381341 (_24474 : real) : (term94 _24474) = (term94 _24474).
Proof. exact (eq_refl (term94 _24474)). Qed.
Lemma lem1381342 (_24474 : real) (_24473 : real) : (term91 _24473 _24474) = (term95 _24474 _24473).
Proof. exact (MK_COMB (@lem1381341 _24474) (@lem1381335 _24474 _24473)). Qed.
Lemma lem1381346 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1381347 (_24474 : real) (_24473 : real) : (term95 _24474 _24473) = (term96 _24474 _24473).
Proof. exact (@lem1381346 (term38 _24473 _24474) (term73 _24474) (term72 _24473)). Qed.
Lemma lem1381363 (_24474 : real) (_24473 : real) : (term91 _24473 _24474) = (term96 _24474 _24473).
Proof. exact (TRANS (@lem1381342 _24474 _24473) (@lem1381347 _24474 _24473)). Qed.
Lemma lem1381364 (_24474 : real) (_24473 : real) : (term71 _24473 _24474) = (term96 _24474 _24473).
Proof. exact (TRANS (@lem1381320 _24473 _24474) (@lem1381363 _24474 _24473)). Qed.
Lemma lem1381365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1381366 (_24474 : real) (_24473 : real) : (term97 _24473 _24474) = (term98 _24474 _24473).
Proof. exact (MK_COMB (@lem1381365) (@lem1381364 _24474 _24473)). Qed.
Lemma lem1381380 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1381381 (_24474 : real) (_24473 : real) : (term55 _24473 _24474) = (term99 _24474 _24473).
Proof. exact (@lem1381380 (term73 _24474) (term72 _24473)). Qed.
Lemma lem1381387 (_24473 : real) (_24474 : real) : (term100 _24473 _24474) = (term100 _24473 _24474).
Proof. exact (eq_refl (term100 _24473 _24474)). Qed.
Lemma lem1381388 (_24474 : real) (_24473 : real) : (term101 _24473 _24474) = (term96 _24474 _24473).
Proof. exact (MK_COMB (@lem1381387 _24473 _24474) (@lem1381381 _24474 _24473)). Qed.
Lemma lem1381399 (_24474 : real) (_24473 : real) : ((term71 _24473 _24474) = (term101 _24473 _24474)) = ((term96 _24474 _24473) = (term96 _24474 _24473)).
Proof. exact (MK_COMB (@lem1381366 _24474 _24473) (@lem1381388 _24474 _24473)). Qed.
Lemma lem1381401 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1381402 (x : Prop) : (x = x) = True.
Proof. exact (@lem1381401 Prop x). Qed.
Lemma lem1381403 (_24474 : real) (_24473 : real) : ((term96 _24474 _24473) = (term96 _24474 _24473)) = True.
Proof. exact (@lem1381402 (term96 _24474 _24473)). Qed.
Lemma lem1381404 (_24473 : real) (_24474 : real) : ((term71 _24473 _24474) = (term101 _24473 _24474)) = True.
Proof. exact (TRANS (@lem1381399 _24474 _24473) (@lem1381403 _24474 _24473)). Qed.
Lemma lem1381405 (_24473 : real) (_24474 : real) : True = ((term71 _24473 _24474) = (term101 _24473 _24474)).
Proof. exact (SYM (@lem1381404 _24473 _24474)). Qed.
Lemma lem1381406 (_24473 : real) (_24474 : real) : (term71 _24473 _24474) = (term101 _24473 _24474).
Proof. exact (EQ_MP (@lem1381405 _24473 _24474) (@lem0)). Qed.
Lemma lem1381407 (_24473 : real) (_24474 : real) (h1 : term17) : term101 _24473 _24474.
Proof. exact (EQ_MP (@lem1381406 _24473 _24474) (@lem1381204 _24473 _24474 h1)). Qed.
Lemma lem1381409 (b : Prop) (a : Prop) : (a \/ b) = (term102 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1381410 (_24473 : real) (_24474 : real) : (term101 _24473 _24474) = (term103 _24473 _24474).
Proof. exact (@lem1381409 (term55 _24473 _24474) (term38 _24473 _24474)). Qed.
Lemma lem1381412 (a : Prop) (b : Prop) : (term104 a b) = (term105 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1381413 (_24473 : real) (_24474 : real) : (term106 _24473 _24474) = (term107 _24473 _24474).
Proof. exact (@lem1381412 (term72 _24473) (term73 _24474)). Qed.
Lemma lem1381415 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1381416 (_24473 : real) : (term109 _24473) = (term56 _24473).
Proof. exact (@lem1381415 (term56 _24473)). Qed.
Lemma lem1381417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1381418 (_24473 : real) : (term110 _24473) = (term111 _24473).
Proof. exact (MK_COMB (@lem1381417) (@lem1381416 _24473)). Qed.
Lemma lem1381420 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1381421 (_24474 : real) : (term112 _24474) = (term57 _24474).
Proof. exact (@lem1381420 (term57 _24474)). Qed.
Lemma lem1381422 (_24473 : real) (_24474 : real) : (term107 _24473 _24474) = (term62 _24473 _24474).
Proof. exact (MK_COMB (@lem1381418 _24473) (@lem1381421 _24474)). Qed.
Lemma lem1381423 (_24473 : real) (_24474 : real) : (term106 _24473 _24474) = (term62 _24473 _24474).
Proof. exact (TRANS (@lem1381413 _24473 _24474) (@lem1381422 _24473 _24474)). Qed.
Lemma lem1381424 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1381425 (_24473 : real) (_24474 : real) : (term113 _24473 _24474) = (term114 _24473 _24474).
Proof. exact (MK_COMB (@lem1381424) (@lem1381423 _24473 _24474)). Qed.
Lemma lem1381426 (_24473 : real) (_24474 : real) : (term38 _24473 _24474) = (term38 _24473 _24474).
Proof. exact (eq_refl (term38 _24473 _24474)). Qed.
Lemma lem1381427 (_24473 : real) (_24474 : real) : (term103 _24473 _24474) = (term23 _24473 _24474).
Proof. exact (MK_COMB (@lem1381425 _24473 _24474) (@lem1381426 _24473 _24474)). Qed.
Lemma lem1381428 (_24473 : real) (_24474 : real) : (term101 _24473 _24474) = (term23 _24473 _24474).
Proof. exact (TRANS (@lem1381410 _24473 _24474) (@lem1381427 _24473 _24474)). Qed.
Lemma lem1381430 (x : real) (y : real) (h1 : term36 x y) : term62 y x.
Proof. exact (conj (@lem1381306 x y h1) (@lem1381313 x y h1)). Qed.
Lemma lem1381432 (_24473 : real) (_24474 : real) (h1 : term17) : term23 _24473 _24474.
Proof. exact (EQ_MP (@lem1381428 _24473 _24474) (@lem1381407 _24473 _24474 h1)). Qed.
Lemma lem1381433 (y : real) (x : real) (h1 : term17) : term23 y x.
Proof. exact (@lem1381432 y x h1). Qed.
Lemma lem1381436 (x : real) (y : real) (h1 : term17) (h2 : term36 x y) : term38 y x.
Proof. exact (@lem1381433 y x h1 (@lem1381430 x y h2)). Qed.
Lemma lem1381437 (x : real) (y : real) (h1 : term17) (h2 : term36 x y) : term115 y x.
Proof. exact (fun h0 : term74 y x => @lem1381436 x y h1 h2). Qed.
Lemma lem1381439 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381440 (y : real) (x : real) : (term115 y x) = (term38 y x).
Proof. exact (@lem1381439 (term38 y x)). Qed.
Lemma lem1381441 (x : real) (y : real) (h1 : term17) (h2 : term36 x y) : term38 y x.
Proof. exact (EQ_MP (@lem1381440 y x) (@lem1381437 x y h1 h2)). Qed.
Lemma lem1381459 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1381460 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term80 _24481 _24482 _24479 _24480) = (term116 _24481 _24482 _24479 _24480).
Proof. exact (@lem1381459 (real_lt _24481 _24482) (term117 _24480 _24482) (term118 _24479 _24480)). Qed.
Lemma lem1381478 (_24479 : real) (_24481 : real) : (term119 _24479 _24481) = (term119 _24479 _24481).
Proof. exact (eq_refl (term119 _24479 _24481)). Qed.
Lemma lem1381479 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term82 _24481 _24482 _24479 _24480) = (term120 _24481 _24482 _24479 _24480).
Proof. exact (MK_COMB (@lem1381478 _24479 _24481) (@lem1381460 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381483 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1381484 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term120 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480).
Proof. exact (@lem1381483 (real_lt _24481 _24482) (term117 _24479 _24481) (term122 _24482 _24479 _24480)). Qed.
Lemma lem1381514 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term82 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480).
Proof. exact (TRANS (@lem1381479 _24481 _24482 _24479 _24480) (@lem1381484 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1381516 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term123 _24481 _24482 _24479 _24480) = (term124 _24481 _24482 _24479 _24480).
Proof. exact (MK_COMB (@lem1381515) (@lem1381514 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381546 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term121 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480).
Proof. exact (eq_refl (term121 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381547 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : ((term82 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480)) = ((term121 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480)).
Proof. exact (MK_COMB (@lem1381516 _24481 _24482 _24479 _24480) (@lem1381546 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1381550 (x : Prop) : (x = x) = True.
Proof. exact (@lem1381549 Prop x). Qed.
Lemma lem1381551 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : ((term121 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480)) = True.
Proof. exact (@lem1381550 (term121 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381552 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : ((term82 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480)) = True.
Proof. exact (TRANS (@lem1381547 _24481 _24482 _24479 _24480) (@lem1381551 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381553 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : True = ((term82 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480)).
Proof. exact (SYM (@lem1381552 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381554 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term82 _24481 _24482 _24479 _24480) = (term121 _24481 _24482 _24479 _24480).
Proof. exact (EQ_MP (@lem1381553 _24481 _24482 _24479 _24480) (@lem0)). Qed.
Lemma lem1381555 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : term121 _24481 _24482 _24479 _24480.
Proof. exact (EQ_MP (@lem1381554 _24481 _24482 _24479 _24480) (@lem1381248 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381557 (b : Prop) (a : Prop) : (a \/ b) = (term102 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1381558 (_24479 : real) (_24480 : real) (_24481 : real) (_24482 : real) : (term121 _24481 _24482 _24479 _24480) = (term125 _24479 _24480 _24481 _24482).
Proof. exact (@lem1381557 (term126 _24481 _24482 _24479 _24480) (real_lt _24481 _24482)). Qed.
Lemma lem1381560 (a : Prop) (b : Prop) : (term104 a b) = (term105 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1381561 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term127 _24481 _24482 _24479 _24480) = (term128 _24481 _24482 _24479 _24480).
Proof. exact (@lem1381560 (term117 _24479 _24481) (term122 _24482 _24479 _24480)). Qed.
Lemma lem1381563 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1381564 (_24479 : real) (_24481 : real) : (term129 _24479 _24481) = (_24479 = _24481).
Proof. exact (@lem1381563 (_24479 = _24481)). Qed.
Lemma lem1381565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1381566 (_24479 : real) (_24481 : real) : (term130 _24479 _24481) = (term131 _24479 _24481).
Proof. exact (MK_COMB (@lem1381565) (@lem1381564 _24479 _24481)). Qed.
Lemma lem1381568 (a : Prop) (b : Prop) : (term104 a b) = (term105 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1381569 (_24482 : real) (_24479 : real) (_24480 : real) : (term132 _24482 _24479 _24480) = (term133 _24482 _24479 _24480).
Proof. exact (@lem1381568 (term117 _24480 _24482) (term118 _24479 _24480)). Qed.
Lemma lem1381571 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1381572 (_24480 : real) (_24482 : real) : (term129 _24480 _24482) = (_24480 = _24482).
Proof. exact (@lem1381571 (_24480 = _24482)). Qed.
Lemma lem1381573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1381574 (_24480 : real) (_24482 : real) : (term130 _24480 _24482) = (term131 _24480 _24482).
Proof. exact (MK_COMB (@lem1381573) (@lem1381572 _24480 _24482)). Qed.
Lemma lem1381576 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1381577 (_24479 : real) (_24480 : real) : (term134 _24479 _24480) = (real_lt _24479 _24480).
Proof. exact (@lem1381576 (real_lt _24479 _24480)). Qed.
Lemma lem1381578 (_24482 : real) (_24479 : real) (_24480 : real) : (term133 _24482 _24479 _24480) = (term135 _24482 _24479 _24480).
Proof. exact (MK_COMB (@lem1381574 _24480 _24482) (@lem1381577 _24479 _24480)). Qed.
Lemma lem1381579 (_24482 : real) (_24479 : real) (_24480 : real) : (term132 _24482 _24479 _24480) = (term135 _24482 _24479 _24480).
Proof. exact (TRANS (@lem1381569 _24482 _24479 _24480) (@lem1381578 _24482 _24479 _24480)). Qed.
Lemma lem1381580 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term128 _24481 _24482 _24479 _24480) = (term136 _24481 _24482 _24479 _24480).
Proof. exact (MK_COMB (@lem1381566 _24479 _24481) (@lem1381579 _24482 _24479 _24480)). Qed.
Lemma lem1381581 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term127 _24481 _24482 _24479 _24480) = (term136 _24481 _24482 _24479 _24480).
Proof. exact (TRANS (@lem1381561 _24481 _24482 _24479 _24480) (@lem1381580 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1381583 (_24481 : real) (_24482 : real) (_24479 : real) (_24480 : real) : (term137 _24481 _24482 _24479 _24480) = (term138 _24481 _24482 _24479 _24480).
Proof. exact (MK_COMB (@lem1381582) (@lem1381581 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381584 (_24481 : real) (_24482 : real) : (real_lt _24481 _24482) = (real_lt _24481 _24482).
Proof. exact (eq_refl (real_lt _24481 _24482)). Qed.
Lemma lem1381585 (_24479 : real) (_24480 : real) (_24481 : real) (_24482 : real) : (term125 _24479 _24480 _24481 _24482) = (term139 _24479 _24480 _24481 _24482).
Proof. exact (MK_COMB (@lem1381583 _24481 _24482 _24479 _24480) (@lem1381584 _24481 _24482)). Qed.
Lemma lem1381586 (_24479 : real) (_24480 : real) (_24481 : real) (_24482 : real) : (term121 _24481 _24482 _24479 _24480) = (term139 _24479 _24480 _24481 _24482).
Proof. exact (TRANS (@lem1381558 _24479 _24480 _24481 _24482) (@lem1381585 _24479 _24480 _24481 _24482)). Qed.
Lemma lem1381588 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term140 y x.
Proof. exact (conj (@lem1381299 x y h1) (@lem1381441 x y h2 h3)). Qed.
Lemma lem1381589 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term141 y x.
Proof. exact (conj (@lem1381291) (@lem1381588 x y h1 h2 h3)). Qed.
Lemma lem1381591 (_24479 : real) (_24480 : real) (_24481 : real) (_24482 : real) : term139 _24479 _24480 _24481 _24482.
Proof. exact (EQ_MP (@lem1381586 _24479 _24480 _24481 _24482) (@lem1381555 _24481 _24482 _24479 _24480)). Qed.
Lemma lem1381592 (x : real) (y : real) : term142 x y.
Proof. exact (@lem1381591 term83 (real_add y x) term83 (real_add x y)). Qed.
Lemma lem1381595 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term38 x y.
Proof. exact (@lem1381592 x y (@lem1381589 x y h1 h2 h3)). Qed.
Lemma lem1381596 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term115 x y.
Proof. exact (fun h0 : term74 x y => @lem1381595 x y h1 h2 h3). Qed.
Lemma lem1381598 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381599 (x : real) (y : real) : (term115 x y) = (term38 x y).
Proof. exact (@lem1381598 (term38 x y)). Qed.
Lemma lem1381600 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term38 x y.
Proof. exact (EQ_MP (@lem1381599 x y) (@lem1381596 x y h1 h2 h3)). Qed.
Lemma lem1381603 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1381605 (x : real) (y : real) : (term74 x y) = (term143 x y).
Proof. exact (@lem1381603 (term38 x y)). Qed.
Lemma lem1381608 (x : real) (y : real) (h1 : term36 x y) : term143 x y.
Proof. exact (EQ_MP (@lem1381605 x y) (@lem1381206 x y h1)). Qed.
Lemma lem1381611 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : False.
Proof. exact (@lem1381608 x y h3 (@lem1381600 x y h1 h2 h3)). Qed.
Lemma lem1381612 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term144.
Proof. exact (fun h0 : ~ False => @lem1381611 x y h1 h2 h3). Qed.
Lemma lem1381614 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1381615 : term144 = False.
Proof. exact (@lem1381614 False). Qed.
Lemma lem1381616 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1381615) (@lem1381612 x y h1 h2 h3)). Qed.
Lemma lem1381617 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term30 = False.
Proof. exact (prop_ext (fun h4 : term30 => @lem1381616 x y h1 h2 h3) (fun h4 : False => @lem1381144 h1)). Qed.
Lemma lem1381618 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1381617 x y h1 h2 h3) (@lem1381144 h1)). Qed.
Lemma lem1381619 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : (term36 x y) = False.
Proof. exact (prop_ext (fun h4 : term36 x y => @lem1381618 x y h1 h2 h3) (fun h4 : False => @lem1381130 x y h3)). Qed.
Lemma lem1381620 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1381619 x y h1 h2 h3) (@lem1381130 x y h3)). Qed.
Lemma lem1381621 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : term30 = False.
Proof. exact (prop_ext (fun h4 : term30 => @lem1381620 x y h1 h2 h3) (fun h4 : False => @lem1381042 h1)). Qed.
Lemma lem1381622 (x : real) (y : real) (h1 : term30) (h2 : term17) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1381621 x y h1 h2 h3) (@lem1381042 h1)). Qed.
Lemma lem1381623 (x : real) (h1 : term30) (h2 : term17) (h3 : term47 x) : False.
Proof. exact (ex_elim (@lem1381021 x h3) (fun y : real => fun h0 : term46 x y => @lem1381622 x y h1 h2 h0)). Qed.
Lemma lem1381624 (h1 : term30) (h2 : term17) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1380924 h3) (fun x : real => fun h0 : term52 x => @lem1381623 x h1 h2 h0)). Qed.
Lemma lem1381625 (h1 : term30) (h2 : term17) (h3 : term10) : term30 = False.
Proof. exact (prop_ext (fun h4 : term30 => @lem1381624 h1 h2 h3) (fun h4 : False => @lem1380944 h1)). Qed.
Lemma lem1381626 (h1 : term30) (h2 : term17) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem1381625 h1 h2 h3) (@lem1380944 h1)). Qed.
Lemma lem1381627 (h1 : term30) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1381626 h1 h0 h2). Qed.
Lemma lem1381628 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1381629 (h1 : term30) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1381628) (@lem1381627 h1 h2)). Qed.
Lemma lem1381630 (h1 : term10) : term20.
Proof. exact (fun h0 : term30 => @lem1381629 h0 h1). Qed.
Lemma lem1381631 : term22.
Proof. exact (fun h0 : term10 => @lem1381630 h0). Qed.
Lemma lem1381632 : term11.
Proof. exact (EQ_MP (@lem1380833) (@lem1381631)). Qed.
Lemma lem1381634 : term11.
Proof. exact (@lem1380683 (@lem1381632)). Qed.
Lemma lem1381635 (h1 : term10) : term19.
Proof. exact (@lem1381634 (@lem1380668 h1)). Qed.
Lemma lem1381636 (h1 : term10) : term15.
Proof. exact (@lem1381635 h1 (@lem1338238)). Qed.
Lemma lem1381637 (h1 : term10) : False.
Proof. exact (@lem1381636 h1 (@lem1380653)). Qed.
Lemma lem1381638 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1381637 h1) (fun h2 : False => @lem1380668 h1)). Qed.
Lemma lem1381639 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1381638 h1) (@lem1380668 h1)). Qed.
Lemma lem1381640 : term9.
Proof. exact (fun h0 : term10 => @lem1381639 h0). Qed.
Lemma lem1381641 : term8.
Proof. exact (EQ_MP (@lem1380667) (@lem1381640)). Qed.
