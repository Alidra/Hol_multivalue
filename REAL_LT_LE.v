Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1376696 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1376697 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1376698 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1376697 t1) (@lem1376696 t1)). Qed.
Lemma lem1376699 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1376698 t1 t2). Qed.
Lemma lem1376700 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1376701 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1376700 t1 t2) (@lem1376699 t1 t2)). Qed.
Lemma lem1376702 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1376701 t1 t2 t3). Qed.
Lemma lem1376703 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1376704 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1376703 t1 t2 t3) (@lem1376702 t1 t2 t3)). Qed.
Lemma lem1376705 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1376704 t1 t2 t3)). Qed.
Lemma lem1376707 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1376708 : term8 = term9.
Proof. exact (@lem1376707 term8). Qed.
Lemma lem1376709 : term9 = term8.
Proof. exact (SYM (@lem1376708)). Qed.
Lemma lem1376710 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1376713 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1376714 : term12.
Proof. exact (fun h0 : term11 => @lem1376713 h0). Qed.
Lemma lem1376715 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1376716 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1376717 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1376715 h2 (@lem1376716 h1)). Qed.
Lemma lem1376718 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1376717 h1 h0). Qed.
Lemma lem1376719 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1376720 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1376718 h1 (@lem1376719 h2)). Qed.
Lemma lem1376721 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1376720 h0 h1). Qed.
Lemma lem1376722 : term14.
Proof. exact (fun h0 : term12 => @lem1376721 h0). Qed.
Lemma lem1376725 : term12.
Proof. exact (@lem1376722 (@lem1376714)). Qed.
Lemma lem1376807 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1376808 : term15 = term16.
Proof. exact (@lem1376807 term17). Qed.
Lemma lem1376817 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1376818 : term19 = term20.
Proof. exact (MK_COMB (@lem1376817) (@lem1376808)). Qed.
Lemma lem1376821 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1376822 : term22 = term23.
Proof. exact (MK_COMB (@lem1376821) (@lem1376818)). Qed.
Lemma lem1376825 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1376832 : term11 = term25.
Proof. exact (MK_COMB (@lem1376825) (@lem1376822)). Qed.
Lemma lem1376839 (y : real) (x : real) : ((real_lt x y) = (term26 y x)) = ((real_lt x y) = (term26 y x)).
Proof. exact (eq_refl ((real_lt x y) = (term26 y x))). Qed.
Lemma lem1376840 (y : real) : (term27 y) = (term27 y).
Proof. exact (fun_ext (fun x : real => @lem1376839 y x)). Qed.
Lemma lem1376841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376842 (y : real) : (term28 y) = (term28 y).
Proof. exact (MK_COMB (@lem1376841) (@lem1376840 y)). Qed.
Lemma lem1376843 : term29 = term29.
Proof. exact (fun_ext (fun y : real => @lem1376842 y)). Qed.
Lemma lem1376844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376845 : term17 = term17.
Proof. exact (MK_COMB (@lem1376844) (@lem1376843)). Qed.
Lemma lem1376846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1376847 : term16 = term16.
Proof. exact (MK_COMB (@lem1376846) (@lem1376845)). Qed.
Lemma lem1376852 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (eq_refl (term30 y x)). Qed.
Lemma lem1376853 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1376852 y x)). Qed.
Lemma lem1376854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376855 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1376854) (@lem1376853 x)). Qed.
Lemma lem1376856 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1376855 x)). Qed.
Lemma lem1376857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376858 : term34 = term34.
Proof. exact (MK_COMB (@lem1376857) (@lem1376856)). Qed.
Lemma lem1376859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1376860 : term18 = term18.
Proof. exact (MK_COMB (@lem1376859) (@lem1376858)). Qed.
Lemma lem1376861 : term20 = term20.
Proof. exact (MK_COMB (@lem1376860) (@lem1376847)). Qed.
Lemma lem1376870 (x : real) (y : real) : ((term35 y x) = (x = y)) = ((term35 y x) = (x = y)).
Proof. exact (eq_refl ((term35 y x) = (x = y))). Qed.
Lemma lem1376871 (x : real) : (term36 x) = (term36 x).
Proof. exact (fun_ext (fun y : real => @lem1376870 x y)). Qed.
Lemma lem1376872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376873 (x : real) : (term37 x) = (term37 x).
Proof. exact (MK_COMB (@lem1376872) (@lem1376871 x)). Qed.
Lemma lem1376874 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1376873 x)). Qed.
Lemma lem1376875 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376876 : term39 = term39.
Proof. exact (MK_COMB (@lem1376875) (@lem1376874)). Qed.
Lemma lem1376877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1376878 : term21 = term21.
Proof. exact (MK_COMB (@lem1376877) (@lem1376876)). Qed.
Lemma lem1376879 : term23 = term23.
Proof. exact (MK_COMB (@lem1376878) (@lem1376861)). Qed.
Lemma lem1376890 (x : real) (y : real) : ((real_lt x y) = (term40 x y)) = ((real_lt x y) = (term40 x y)).
Proof. exact (eq_refl ((real_lt x y) = (term40 x y))). Qed.
Lemma lem1376891 (x : real) : (term41 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1376890 x y)). Qed.
Lemma lem1376892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376893 (x : real) : (term42 x) = (term42 x).
Proof. exact (MK_COMB (@lem1376892) (@lem1376891 x)). Qed.
Lemma lem1376894 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem1376893 x)). Qed.
Lemma lem1376895 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376896 : term8 = term8.
Proof. exact (MK_COMB (@lem1376895) (@lem1376894)). Qed.
Lemma lem1376897 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1376898 : term10 = term10.
Proof. exact (MK_COMB (@lem1376897) (@lem1376896)). Qed.
Lemma lem1376899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1376900 : term24 = term24.
Proof. exact (MK_COMB (@lem1376899) (@lem1376898)). Qed.
Lemma lem1376901 : term25 = term25.
Proof. exact (MK_COMB (@lem1376900) (@lem1376879)). Qed.
Lemma lem1376964 : term11 = term25.
Proof. exact (TRANS (@lem1376832) (@lem1376901)). Qed.
Lemma lem1376965 : term25 = term11.
Proof. exact (SYM (@lem1376964)). Qed.
Lemma lem1376966 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1376967 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem1376968 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1376969 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1376977 (x : real) (y : real) : (term44 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem1376979 (x : real) (y : real) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1376980 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1376979 x y) (@lem1376977 x y)). Qed.
Lemma lem1376981 (x : real) (y : real) : (term48 x y) = (term46 x y).
Proof. exact (@lem17045 (real_le x y) (term49 x y)). Qed.
Lemma lem1376982 (x : real) (y : real) : (term48 x y) = (term47 x y).
Proof. exact (TRANS (@lem1376981 x y) (@lem1376980 x y)). Qed.
Lemma lem1376988 (x : real) (y : real) : (term50 x y) = (term50 x y).
Proof. exact (eq_refl (term50 x y)). Qed.
Lemma lem1376990 (x : real) (y : real) : (term51 x y) = (term51 x y).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1376991 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1376990 x y) (@lem1376982 x y)). Qed.
Lemma lem1376992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1376993 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1376992) (@lem1376991 x y)). Qed.
Lemma lem1376994 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1376993 x y) (@lem1376988 x y)). Qed.
Lemma lem1376995 (x : real) (y : real) : (term58 x y) = (term56 x y).
Proof. exact (@lem17646 (real_lt x y) (term40 x y)). Qed.
Lemma lem1376996 (x : real) (y : real) : (term58 x y) = (term57 x y).
Proof. exact (TRANS (@lem1376995 x y) (@lem1376994 x y)). Qed.
Lemma lem1376997 (P : real -> Prop) : (term59 P) = (term60 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1376998 (x : real) : (term61 x) = (term62 x).
Proof. exact (@lem1376997 (term41 x)). Qed.
Lemma lem1376999 (x : real) (y : real) : (term63 x y) = ((real_lt x y) = (term40 x y)).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1377000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1377001 (x : real) (y : real) : (term64 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1377000) (@lem1376999 x y)). Qed.
Lemma lem1377002 (x : real) (y : real) : (term64 x y) = (term57 x y).
Proof. exact (TRANS (@lem1377001 x y) (@lem1376996 x y)). Qed.
Lemma lem1377003 (x : real) : (term65 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1377002 x y)). Qed.
Lemma lem1377004 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377005 (x : real) : (term62 x) = (term67 x).
Proof. exact (MK_COMB (@lem1377004) (@lem1377003 x)). Qed.
Lemma lem1377006 (x : real) : (term61 x) = (term67 x).
Proof. exact (TRANS (@lem1376998 x) (@lem1377005 x)). Qed.
Lemma lem1377007 (P : real -> Prop) : (term59 P) = (term60 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1377008 : term10 = term68.
Proof. exact (@lem1377007 term43). Qed.
Lemma lem1377009 (x : real) : (term69 x) = (term42 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1377010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1377011 (x : real) : (term70 x) = (term61 x).
Proof. exact (MK_COMB (@lem1377010) (@lem1377009 x)). Qed.
Lemma lem1377012 (x : real) : (term70 x) = (term67 x).
Proof. exact (TRANS (@lem1377011 x) (@lem1377006 x)). Qed.
Lemma lem1377013 : term71 = term72.
Proof. exact (fun_ext (fun x : real => @lem1377012 x)). Qed.
Lemma lem1377014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377015 : term68 = term73.
Proof. exact (MK_COMB (@lem1377014) (@lem1377013)). Qed.
Lemma lem1377016 : term10 = term73.
Proof. exact (TRANS (@lem1377008) (@lem1377015)). Qed.
Lemma lem1377022 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1377023 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1377022 real P Q). Qed.
Lemma lem1377024 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1377023 (term80 x) (term81 x)). Qed.
Lemma lem1377025 (x : real) (y : real) : (term82 x y) = (term53 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1377026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377027 (x : real) (y : real) : (term83 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1377026) (@lem1377025 x y)). Qed.
Lemma lem1377028 (x : real) (y : real) : (term84 x y) = (term50 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1377029 (x : real) (y : real) : (term85 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1377027 x y) (@lem1377028 x y)). Qed.
Lemma lem1377030 (x : real) : (term86 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1377029 x y)). Qed.
Lemma lem1377031 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377032 (x : real) : (term78 x) = (term67 x).
Proof. exact (MK_COMB (@lem1377031) (@lem1377030 x)). Qed.
Lemma lem1377033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377034 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1377033) (@lem1377032 x)). Qed.
Lemma lem1377035 (x : real) (y : real) : (term82 x y) = (term53 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1377036 (x : real) : (term89 x) = (term80 x).
Proof. exact (fun_ext (fun y : real => @lem1377035 x y)). Qed.
Lemma lem1377037 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377038 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem1377037) (@lem1377036 x)). Qed.
Lemma lem1377039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377040 (x : real) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem1377039) (@lem1377038 x)). Qed.
Lemma lem1377041 (x : real) (y : real) : (term84 x y) = (term50 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1377042 (x : real) : (term94 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1377041 x y)). Qed.
Lemma lem1377043 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377044 (x : real) : (term95 x) = (term96 x).
Proof. exact (MK_COMB (@lem1377043) (@lem1377042 x)). Qed.
Lemma lem1377045 (x : real) : (term79 x) = (term97 x).
Proof. exact (MK_COMB (@lem1377040 x) (@lem1377044 x)). Qed.
Lemma lem1377046 (x : real) : ((term78 x) = (term79 x)) = ((term67 x) = (term97 x)).
Proof. exact (MK_COMB (@lem1377034 x) (@lem1377045 x)). Qed.
Lemma lem1377047 (x : real) : (term67 x) = (term97 x).
Proof. exact (EQ_MP (@lem1377046 x) (@lem1377024 x)). Qed.
Lemma lem1377144 : term72 = term98.
Proof. exact (fun_ext (fun x : real => @lem1377047 x)). Qed.
Lemma lem1377145 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377146 : term73 = term99.
Proof. exact (MK_COMB (@lem1377145) (@lem1377144)). Qed.
Lemma lem1377148 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1377149 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1377148 real P Q). Qed.
Lemma lem1377150 : term100 = term101.
Proof. exact (@lem1377149 term102 term103). Qed.
Lemma lem1377151 (x : real) : (term104 x) = (term91 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1377152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377153 (x : real) : (term105 x) = (term93 x).
Proof. exact (MK_COMB (@lem1377152) (@lem1377151 x)). Qed.
Lemma lem1377154 (x : real) : (term106 x) = (term96 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1377155 (x : real) : (term107 x) = (term97 x).
Proof. exact (MK_COMB (@lem1377153 x) (@lem1377154 x)). Qed.
Lemma lem1377156 : term108 = term98.
Proof. exact (fun_ext (fun x : real => @lem1377155 x)). Qed.
Lemma lem1377157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377158 : term100 = term99.
Proof. exact (MK_COMB (@lem1377157) (@lem1377156)). Qed.
Lemma lem1377159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377160 : term109 = term110.
Proof. exact (MK_COMB (@lem1377159) (@lem1377158)). Qed.
Lemma lem1377161 (x : real) : (term104 x) = (term91 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1377162 : term111 = term102.
Proof. exact (fun_ext (fun x : real => @lem1377161 x)). Qed.
Lemma lem1377163 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377164 : term112 = term113.
Proof. exact (MK_COMB (@lem1377163) (@lem1377162)). Qed.
Lemma lem1377165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377166 : term114 = term115.
Proof. exact (MK_COMB (@lem1377165) (@lem1377164)). Qed.
Lemma lem1377167 (x : real) : (term106 x) = (term96 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1377168 : term116 = term103.
Proof. exact (fun_ext (fun x : real => @lem1377167 x)). Qed.
Lemma lem1377169 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377170 : term117 = term118.
Proof. exact (MK_COMB (@lem1377169) (@lem1377168)). Qed.
Lemma lem1377171 : term101 = term119.
Proof. exact (MK_COMB (@lem1377166) (@lem1377170)). Qed.
Lemma lem1377172 : (term100 = term101) = (term99 = term119).
Proof. exact (MK_COMB (@lem1377160) (@lem1377171)). Qed.
Lemma lem1377173 : term99 = term119.
Proof. exact (EQ_MP (@lem1377172) (@lem1377150)). Qed.
Lemma lem1377278 : term73 = term119.
Proof. exact (TRANS (@lem1377146) (@lem1377173)). Qed.
Lemma lem1377280 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1377281 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1377280 real P Q). Qed.
Lemma lem1377282 : term101 = term100.
Proof. exact (@lem1377281 term102 term103). Qed.
Lemma lem1377283 (x : real) : (term104 x) = (term91 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1377284 : term111 = term102.
Proof. exact (fun_ext (fun x : real => @lem1377283 x)). Qed.
Lemma lem1377285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377286 : term112 = term113.
Proof. exact (MK_COMB (@lem1377285) (@lem1377284)). Qed.
Lemma lem1377287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377288 : term114 = term115.
Proof. exact (MK_COMB (@lem1377287) (@lem1377286)). Qed.
Lemma lem1377289 (x : real) : (term106 x) = (term96 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1377290 : term116 = term103.
Proof. exact (fun_ext (fun x : real => @lem1377289 x)). Qed.
Lemma lem1377291 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377292 : term117 = term118.
Proof. exact (MK_COMB (@lem1377291) (@lem1377290)). Qed.
Lemma lem1377293 : term101 = term119.
Proof. exact (MK_COMB (@lem1377288) (@lem1377292)). Qed.
Lemma lem1377294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377295 : term120 = term121.
Proof. exact (MK_COMB (@lem1377294) (@lem1377293)). Qed.
Lemma lem1377296 (x : real) : (term104 x) = (term91 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1377297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377298 (x : real) : (term105 x) = (term93 x).
Proof. exact (MK_COMB (@lem1377297) (@lem1377296 x)). Qed.
Lemma lem1377299 (x : real) : (term106 x) = (term96 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1377300 (x : real) : (term107 x) = (term97 x).
Proof. exact (MK_COMB (@lem1377298 x) (@lem1377299 x)). Qed.
Lemma lem1377301 : term108 = term98.
Proof. exact (fun_ext (fun x : real => @lem1377300 x)). Qed.
Lemma lem1377302 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377303 : term100 = term99.
Proof. exact (MK_COMB (@lem1377302) (@lem1377301)). Qed.
Lemma lem1377304 : (term101 = term100) = (term119 = term99).
Proof. exact (MK_COMB (@lem1377295) (@lem1377303)). Qed.
Lemma lem1377305 : term119 = term99.
Proof. exact (EQ_MP (@lem1377304) (@lem1377282)). Qed.
Lemma lem1377307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1377308 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1377307 real P Q). Qed.
Lemma lem1377309 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1377308 (term80 x) (term81 x)). Qed.
Lemma lem1377310 (x : real) (y : real) : (term82 x y) = (term53 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1377311 (x : real) : (term89 x) = (term80 x).
Proof. exact (fun_ext (fun y : real => @lem1377310 x y)). Qed.
Lemma lem1377312 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377313 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem1377312) (@lem1377311 x)). Qed.
Lemma lem1377314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377315 (x : real) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem1377314) (@lem1377313 x)). Qed.
Lemma lem1377316 (x : real) (y : real) : (term84 x y) = (term50 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1377317 (x : real) : (term94 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1377316 x y)). Qed.
Lemma lem1377318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377319 (x : real) : (term95 x) = (term96 x).
Proof. exact (MK_COMB (@lem1377318) (@lem1377317 x)). Qed.
Lemma lem1377320 (x : real) : (term79 x) = (term97 x).
Proof. exact (MK_COMB (@lem1377315 x) (@lem1377319 x)). Qed.
Lemma lem1377321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377322 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1377321) (@lem1377320 x)). Qed.
Lemma lem1377323 (x : real) (y : real) : (term82 x y) = (term53 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1377324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377325 (x : real) (y : real) : (term83 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1377324) (@lem1377323 x y)). Qed.
Lemma lem1377326 (x : real) (y : real) : (term84 x y) = (term50 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1377327 (x : real) (y : real) : (term85 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1377325 x y) (@lem1377326 x y)). Qed.
Lemma lem1377328 (x : real) : (term86 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1377327 x y)). Qed.
Lemma lem1377329 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377330 (x : real) : (term78 x) = (term67 x).
Proof. exact (MK_COMB (@lem1377329) (@lem1377328 x)). Qed.
Lemma lem1377331 (x : real) : ((term79 x) = (term78 x)) = ((term97 x) = (term67 x)).
Proof. exact (MK_COMB (@lem1377322 x) (@lem1377330 x)). Qed.
Lemma lem1377332 (x : real) : (term97 x) = (term67 x).
Proof. exact (EQ_MP (@lem1377331 x) (@lem1377309 x)). Qed.
Lemma lem1377333 : term98 = term72.
Proof. exact (fun_ext (fun x : real => @lem1377332 x)). Qed.
Lemma lem1377334 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1377335 : term99 = term73.
Proof. exact (MK_COMB (@lem1377334) (@lem1377333)). Qed.
Lemma lem1377336 : term119 = term73.
Proof. exact (TRANS (@lem1377305) (@lem1377335)). Qed.
Lemma lem1377337 : term73 = term73.
Proof. exact (TRANS (@lem1377278) (@lem1377336)). Qed.
Lemma lem1377338 : term10 = term73.
Proof. exact (TRANS (@lem1377016) (@lem1377337)). Qed.
Lemma lem1377339 (h1 : term10) : term73.
Proof. exact (EQ_MP (@lem1377338) (@lem1376966 h1)). Qed.
Lemma lem1377348 (y : real) (x : real) : (term124 y x) = (term125 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem1377353 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1377354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1377355 (y : real) (x : real) : (term126 y x) = (term127 y x).
Proof. exact (MK_COMB (@lem1377354) (@lem1377348 y x)). Qed.
Lemma lem1377356 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1377355 y x) (@lem1377353 x y)). Qed.
Lemma lem1377361 (x : real) (y : real) : (term130 x y) = (term130 x y).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem1377362 (x : real) (y : real) : (term131 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1377361 x y) (@lem1377356 x y)). Qed.
Lemma lem1377363 (x : real) (y : real) : ((term35 y x) = (x = y)) = (term131 x y).
Proof. exact (@lem17784 (term35 y x) (x = y)). Qed.
Lemma lem1377364 (x : real) (y : real) : ((term35 y x) = (x = y)) = (term132 x y).
Proof. exact (TRANS (@lem1377363 x y) (@lem1377362 x y)). Qed.
Lemma lem1377365 (x : real) : (term36 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1377364 x y)). Qed.
Lemma lem1377366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377367 (x : real) : (term37 x) = (term134 x).
Proof. exact (MK_COMB (@lem1377366) (@lem1377365 x)). Qed.
Lemma lem1377368 : term38 = term135.
Proof. exact (fun_ext (fun x : real => @lem1377367 x)). Qed.
Lemma lem1377369 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377370 : term39 = term136.
Proof. exact (MK_COMB (@lem1377369) (@lem1377368)). Qed.
Lemma lem1377376 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1377377 (P : real -> Prop) (Q : real -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem1377376 real P Q). Qed.
Lemma lem1377378 (x : real) : (term141 x) = (term142 x).
Proof. exact (@lem1377377 (term143 x) (term144 x)). Qed.
Lemma lem1377379 (x : real) (y : real) : (term145 x y) = (term146 x y).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1377380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377381 (x : real) (y : real) : (term147 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1377380) (@lem1377379 x y)). Qed.
Lemma lem1377382 (x : real) (y : real) : (term148 x y) = (term129 x y).
Proof. exact (eq_refl (term148 x y)). Qed.
Lemma lem1377383 (x : real) (y : real) : (term149 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1377381 x y) (@lem1377382 x y)). Qed.
Lemma lem1377384 (x : real) : (term150 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1377383 x y)). Qed.
Lemma lem1377385 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377386 (x : real) : (term141 x) = (term134 x).
Proof. exact (MK_COMB (@lem1377385) (@lem1377384 x)). Qed.
Lemma lem1377387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377388 (x : real) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem1377387) (@lem1377386 x)). Qed.
Lemma lem1377389 (x : real) (y : real) : (term145 x y) = (term146 x y).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1377390 (x : real) : (term153 x) = (term143 x).
Proof. exact (fun_ext (fun y : real => @lem1377389 x y)). Qed.
Lemma lem1377391 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377392 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1377391) (@lem1377390 x)). Qed.
Lemma lem1377393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377394 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1377393) (@lem1377392 x)). Qed.
Lemma lem1377395 (x : real) (y : real) : (term148 x y) = (term129 x y).
Proof. exact (eq_refl (term148 x y)). Qed.
Lemma lem1377396 (x : real) : (term158 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1377395 x y)). Qed.
Lemma lem1377397 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377398 (x : real) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem1377397) (@lem1377396 x)). Qed.
Lemma lem1377399 (x : real) : (term142 x) = (term161 x).
Proof. exact (MK_COMB (@lem1377394 x) (@lem1377398 x)). Qed.
Lemma lem1377400 (x : real) : ((term141 x) = (term142 x)) = ((term134 x) = (term161 x)).
Proof. exact (MK_COMB (@lem1377388 x) (@lem1377399 x)). Qed.
Lemma lem1377401 (x : real) : (term134 x) = (term161 x).
Proof. exact (EQ_MP (@lem1377400 x) (@lem1377378 x)). Qed.
Lemma lem1377498 : term135 = term162.
Proof. exact (fun_ext (fun x : real => @lem1377401 x)). Qed.
Lemma lem1377499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377500 : term136 = term163.
Proof. exact (MK_COMB (@lem1377499) (@lem1377498)). Qed.
Lemma lem1377502 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1377503 (P : real -> Prop) (Q : real -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem1377502 real P Q). Qed.
Lemma lem1377504 : term164 = term165.
Proof. exact (@lem1377503 term166 term167). Qed.
Lemma lem1377505 (x : real) : (term168 x) = (term155 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1377506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377507 (x : real) : (term169 x) = (term157 x).
Proof. exact (MK_COMB (@lem1377506) (@lem1377505 x)). Qed.
Lemma lem1377508 (x : real) : (term170 x) = (term160 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1377509 (x : real) : (term171 x) = (term161 x).
Proof. exact (MK_COMB (@lem1377507 x) (@lem1377508 x)). Qed.
Lemma lem1377510 : term172 = term162.
Proof. exact (fun_ext (fun x : real => @lem1377509 x)). Qed.
Lemma lem1377511 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377512 : term164 = term163.
Proof. exact (MK_COMB (@lem1377511) (@lem1377510)). Qed.
Lemma lem1377513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377514 : term173 = term174.
Proof. exact (MK_COMB (@lem1377513) (@lem1377512)). Qed.
Lemma lem1377515 (x : real) : (term168 x) = (term155 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1377516 : term175 = term166.
Proof. exact (fun_ext (fun x : real => @lem1377515 x)). Qed.
Lemma lem1377517 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377518 : term176 = term177.
Proof. exact (MK_COMB (@lem1377517) (@lem1377516)). Qed.
Lemma lem1377519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377520 : term178 = term179.
Proof. exact (MK_COMB (@lem1377519) (@lem1377518)). Qed.
Lemma lem1377521 (x : real) : (term170 x) = (term160 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1377522 : term180 = term167.
Proof. exact (fun_ext (fun x : real => @lem1377521 x)). Qed.
Lemma lem1377523 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377524 : term181 = term182.
Proof. exact (MK_COMB (@lem1377523) (@lem1377522)). Qed.
Lemma lem1377525 : term165 = term183.
Proof. exact (MK_COMB (@lem1377520) (@lem1377524)). Qed.
Lemma lem1377526 : (term164 = term165) = (term163 = term183).
Proof. exact (MK_COMB (@lem1377514) (@lem1377525)). Qed.
Lemma lem1377527 : term163 = term183.
Proof. exact (EQ_MP (@lem1377526) (@lem1377504)). Qed.
Lemma lem1377634 : term136 = term183.
Proof. exact (TRANS (@lem1377500) (@lem1377527)). Qed.
Lemma lem1377635 : term39 = term183.
Proof. exact (TRANS (@lem1377370) (@lem1377634)). Qed.
Lemma lem1377636 (h1 : term39) : term183.
Proof. exact (EQ_MP (@lem1377635) (@lem1376967 h1)). Qed.
Lemma lem1377641 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (eq_refl (term30 y x)). Qed.
Lemma lem1377642 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1377641 y x)). Qed.
Lemma lem1377643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377644 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1377643) (@lem1377642 x)). Qed.
Lemma lem1377645 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1377644 x)). Qed.
Lemma lem1377646 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377703 : term34 = term34.
Proof. exact (MK_COMB (@lem1377646) (@lem1377645)). Qed.
Lemma lem1377704 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1377703) (@lem1376968 h1)). Qed.
Lemma lem1377710 (y : real) (x : real) : (term184 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1377713 (y : real) (x : real) : (term185 y x) = (term185 y x).
Proof. exact (eq_refl (term185 y x)). Qed.
Lemma lem1377715 (x : real) (y : real) : (term186 x y) = (term186 x y).
Proof. exact (eq_refl (term186 x y)). Qed.
Lemma lem1377716 (y : real) (x : real) : (term187 y x) = (term188 y x).
Proof. exact (MK_COMB (@lem1377715 x y) (@lem1377710 y x)). Qed.
Lemma lem1377717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377718 (y : real) (x : real) : (term189 y x) = (term190 y x).
Proof. exact (MK_COMB (@lem1377717) (@lem1377716 y x)). Qed.
Lemma lem1377719 (y : real) (x : real) : (term191 y x) = (term192 y x).
Proof. exact (MK_COMB (@lem1377718 y x) (@lem1377713 y x)). Qed.
Lemma lem1377720 (y : real) (x : real) : ((real_lt x y) = (term26 y x)) = (term191 y x).
Proof. exact (@lem17784 (real_lt x y) (term26 y x)). Qed.
Lemma lem1377721 (y : real) (x : real) : ((real_lt x y) = (term26 y x)) = (term192 y x).
Proof. exact (TRANS (@lem1377720 y x) (@lem1377719 y x)). Qed.
Lemma lem1377722 (y : real) : (term27 y) = (term193 y).
Proof. exact (fun_ext (fun x : real => @lem1377721 y x)). Qed.
Lemma lem1377723 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377724 (y : real) : (term28 y) = (term194 y).
Proof. exact (MK_COMB (@lem1377723) (@lem1377722 y)). Qed.
Lemma lem1377725 : term29 = term195.
Proof. exact (fun_ext (fun y : real => @lem1377724 y)). Qed.
Lemma lem1377726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377727 : term17 = term196.
Proof. exact (MK_COMB (@lem1377726) (@lem1377725)). Qed.
Lemma lem1377733 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1377734 (P : real -> Prop) (Q : real -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem1377733 real P Q). Qed.
Lemma lem1377735 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1377734 (term199 y) (term200 y)). Qed.
Lemma lem1377736 (y : real) (x : real) : (term201 y x) = (term188 y x).
Proof. exact (eq_refl (term201 y x)). Qed.
Lemma lem1377737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377738 (y : real) (x : real) : (term202 y x) = (term190 y x).
Proof. exact (MK_COMB (@lem1377737) (@lem1377736 y x)). Qed.
Lemma lem1377739 (y : real) (x : real) : (term203 y x) = (term185 y x).
Proof. exact (eq_refl (term203 y x)). Qed.
Lemma lem1377740 (y : real) (x : real) : (term204 y x) = (term192 y x).
Proof. exact (MK_COMB (@lem1377738 y x) (@lem1377739 y x)). Qed.
Lemma lem1377741 (y : real) : (term205 y) = (term193 y).
Proof. exact (fun_ext (fun x : real => @lem1377740 y x)). Qed.
Lemma lem1377742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377743 (y : real) : (term197 y) = (term194 y).
Proof. exact (MK_COMB (@lem1377742) (@lem1377741 y)). Qed.
Lemma lem1377744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377745 (y : real) : (term206 y) = (term207 y).
Proof. exact (MK_COMB (@lem1377744) (@lem1377743 y)). Qed.
Lemma lem1377746 (y : real) (x : real) : (term201 y x) = (term188 y x).
Proof. exact (eq_refl (term201 y x)). Qed.
Lemma lem1377747 (y : real) : (term208 y) = (term199 y).
Proof. exact (fun_ext (fun x : real => @lem1377746 y x)). Qed.
Lemma lem1377748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377749 (y : real) : (term209 y) = (term210 y).
Proof. exact (MK_COMB (@lem1377748) (@lem1377747 y)). Qed.
Lemma lem1377750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377751 (y : real) : (term211 y) = (term212 y).
Proof. exact (MK_COMB (@lem1377750) (@lem1377749 y)). Qed.
Lemma lem1377752 (y : real) (x : real) : (term203 y x) = (term185 y x).
Proof. exact (eq_refl (term203 y x)). Qed.
Lemma lem1377753 (y : real) : (term213 y) = (term200 y).
Proof. exact (fun_ext (fun x : real => @lem1377752 y x)). Qed.
Lemma lem1377754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377755 (y : real) : (term214 y) = (term215 y).
Proof. exact (MK_COMB (@lem1377754) (@lem1377753 y)). Qed.
Lemma lem1377756 (y : real) : (term198 y) = (term216 y).
Proof. exact (MK_COMB (@lem1377751 y) (@lem1377755 y)). Qed.
Lemma lem1377757 (y : real) : ((term197 y) = (term198 y)) = ((term194 y) = (term216 y)).
Proof. exact (MK_COMB (@lem1377745 y) (@lem1377756 y)). Qed.
Lemma lem1377758 (y : real) : (term194 y) = (term216 y).
Proof. exact (EQ_MP (@lem1377757 y) (@lem1377735 y)). Qed.
Lemma lem1377855 : term195 = term217.
Proof. exact (fun_ext (fun y : real => @lem1377758 y)). Qed.
Lemma lem1377856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377857 : term196 = term218.
Proof. exact (MK_COMB (@lem1377856) (@lem1377855)). Qed.
Lemma lem1377859 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1377860 (P : real -> Prop) (Q : real -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem1377859 real P Q). Qed.
Lemma lem1377861 : term219 = term220.
Proof. exact (@lem1377860 term221 term222). Qed.
Lemma lem1377862 (y : real) : (term223 y) = (term210 y).
Proof. exact (eq_refl (term223 y)). Qed.
Lemma lem1377863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377864 (y : real) : (term224 y) = (term212 y).
Proof. exact (MK_COMB (@lem1377863) (@lem1377862 y)). Qed.
Lemma lem1377865 (y : real) : (term225 y) = (term215 y).
Proof. exact (eq_refl (term225 y)). Qed.
Lemma lem1377866 (y : real) : (term226 y) = (term216 y).
Proof. exact (MK_COMB (@lem1377864 y) (@lem1377865 y)). Qed.
Lemma lem1377867 : term227 = term217.
Proof. exact (fun_ext (fun y : real => @lem1377866 y)). Qed.
Lemma lem1377868 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377869 : term219 = term218.
Proof. exact (MK_COMB (@lem1377868) (@lem1377867)). Qed.
Lemma lem1377870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1377871 : term228 = term229.
Proof. exact (MK_COMB (@lem1377870) (@lem1377869)). Qed.
Lemma lem1377872 (y : real) : (term223 y) = (term210 y).
Proof. exact (eq_refl (term223 y)). Qed.
Lemma lem1377873 : term230 = term221.
Proof. exact (fun_ext (fun y : real => @lem1377872 y)). Qed.
Lemma lem1377874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377875 : term231 = term232.
Proof. exact (MK_COMB (@lem1377874) (@lem1377873)). Qed.
Lemma lem1377876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1377877 : term233 = term234.
Proof. exact (MK_COMB (@lem1377876) (@lem1377875)). Qed.
Lemma lem1377878 (y : real) : (term225 y) = (term215 y).
Proof. exact (eq_refl (term225 y)). Qed.
Lemma lem1377879 : term235 = term222.
Proof. exact (fun_ext (fun y : real => @lem1377878 y)). Qed.
Lemma lem1377880 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1377881 : term236 = term237.
Proof. exact (MK_COMB (@lem1377880) (@lem1377879)). Qed.
Lemma lem1377882 : term220 = term238.
Proof. exact (MK_COMB (@lem1377877) (@lem1377881)). Qed.
Lemma lem1377883 : (term219 = term220) = (term218 = term238).
Proof. exact (MK_COMB (@lem1377871) (@lem1377882)). Qed.
Lemma lem1377884 : term218 = term238.
Proof. exact (EQ_MP (@lem1377883) (@lem1377861)). Qed.
Lemma lem1377991 : term196 = term238.
Proof. exact (TRANS (@lem1377857) (@lem1377884)). Qed.
Lemma lem1377992 : term17 = term238.
Proof. exact (TRANS (@lem1377727) (@lem1377991)). Qed.
Lemma lem1377993 (h1 : term17) : term238.
Proof. exact (EQ_MP (@lem1377992) (@lem1376969 h1)). Qed.
Lemma lem1377994 (x : real) (h1 : term67 x) : term67 x.
Proof. exact (h1). Qed.
Lemma lem1378020 (x : real) (y : real) : (term129 x y) = (term129 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1378021 (x : real) : (term144 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1378020 x y)). Qed.
Lemma lem1378022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378023 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1378022) (@lem1378021 x)). Qed.
Lemma lem1378024 : term167 = term167.
Proof. exact (fun_ext (fun x : real => @lem1378023 x)). Qed.
Lemma lem1378025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378026 : term182 = term182.
Proof. exact (MK_COMB (@lem1378025) (@lem1378024)). Qed.
Lemma lem1378049 (x : real) (y : real) : (term146 x y) = (term146 x y).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem1378050 (x : real) : (term143 x) = (term143 x).
Proof. exact (fun_ext (fun y : real => @lem1378049 x y)). Qed.
Lemma lem1378051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378052 (x : real) : (term155 x) = (term155 x).
Proof. exact (MK_COMB (@lem1378051) (@lem1378050 x)). Qed.
Lemma lem1378053 : term166 = term166.
Proof. exact (fun_ext (fun x : real => @lem1378052 x)). Qed.
Lemma lem1378054 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378055 : term177 = term177.
Proof. exact (MK_COMB (@lem1378054) (@lem1378053)). Qed.
Lemma lem1378056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1378057 : term179 = term179.
Proof. exact (MK_COMB (@lem1378056) (@lem1378055)). Qed.
Lemma lem1378058 : term183 = term183.
Proof. exact (MK_COMB (@lem1378057) (@lem1378026)). Qed.
Lemma lem1378059 (h1 : term39) : term183.
Proof. exact (EQ_MP (@lem1378058) (@lem1377636 h1)). Qed.
Lemma lem1378072 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (eq_refl (term30 y x)). Qed.
Lemma lem1378073 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1378072 y x)). Qed.
Lemma lem1378074 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378075 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1378074) (@lem1378073 x)). Qed.
Lemma lem1378076 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1378075 x)). Qed.
Lemma lem1378077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378078 : term34 = term34.
Proof. exact (MK_COMB (@lem1378077) (@lem1378076)). Qed.
Lemma lem1378079 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1378078) (@lem1377704 h1)). Qed.
Lemma lem1378096 (y : real) (x : real) : (term185 y x) = (term185 y x).
Proof. exact (eq_refl (term185 y x)). Qed.
Lemma lem1378097 (y : real) : (term200 y) = (term200 y).
Proof. exact (fun_ext (fun x : real => @lem1378096 y x)). Qed.
Lemma lem1378098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378099 (y : real) : (term215 y) = (term215 y).
Proof. exact (MK_COMB (@lem1378098) (@lem1378097 y)). Qed.
Lemma lem1378100 : term222 = term222.
Proof. exact (fun_ext (fun y : real => @lem1378099 y)). Qed.
Lemma lem1378101 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378102 : term237 = term237.
Proof. exact (MK_COMB (@lem1378101) (@lem1378100)). Qed.
Lemma lem1378115 (y : real) (x : real) : (term188 y x) = (term188 y x).
Proof. exact (eq_refl (term188 y x)). Qed.
Lemma lem1378116 (y : real) : (term199 y) = (term199 y).
Proof. exact (fun_ext (fun x : real => @lem1378115 y x)). Qed.
Lemma lem1378117 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378118 (y : real) : (term210 y) = (term210 y).
Proof. exact (MK_COMB (@lem1378117) (@lem1378116 y)). Qed.
Lemma lem1378119 : term221 = term221.
Proof. exact (fun_ext (fun y : real => @lem1378118 y)). Qed.
Lemma lem1378120 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378121 : term232 = term232.
Proof. exact (MK_COMB (@lem1378120) (@lem1378119)). Qed.
Lemma lem1378122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1378123 : term234 = term234.
Proof. exact (MK_COMB (@lem1378122) (@lem1378121)). Qed.
Lemma lem1378124 : term238 = term238.
Proof. exact (MK_COMB (@lem1378123) (@lem1378102)). Qed.
Lemma lem1378125 (h1 : term17) : term238.
Proof. exact (EQ_MP (@lem1378124) (@lem1377993 h1)). Qed.
Lemma lem1378177 (x : real) (y : real) (h1 : term57 x y) : term57 x y.
Proof. exact (h1). Qed.
Lemma lem1378178 (h1 : term17) : term237.
Proof. exact (proj2 (@lem1378125 h1)). Qed.
Lemma lem1378179 (h1 : term17) : term232.
Proof. exact (proj1 (@lem1378125 h1)). Qed.
Lemma lem1378180 (h1 : term39) : term182.
Proof. exact (proj2 (@lem1378059 h1)). Qed.
Lemma lem1378181 (h1 : term39) : term177.
Proof. exact (proj1 (@lem1378059 h1)). Qed.
Lemma lem1378182 (x : real) (y : real) (h1 : term53 x y) : term53 x y.
Proof. exact (h1). Qed.
Lemma lem1378183 (x : real) (y : real) (h1 : term50 x y) : term50 x y.
Proof. exact (h1). Qed.
Lemma lem1378184 (x : real) (y : real) (h1 : term53 x y) : term47 x y.
Proof. exact (proj2 (@lem1378182 x y h1)). Qed.
Lemma lem1378188 (x : real) (y : real) (h1 : term50 x y) : term40 x y.
Proof. exact (proj2 (@lem1378183 x y h1)). Qed.
Lemma lem1378199 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (eq_refl (term30 y x)). Qed.
Lemma lem1378200 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1378199 y x)). Qed.
Lemma lem1378201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378202 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1378201) (@lem1378200 x)). Qed.
Lemma lem1378203 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1378202 x)). Qed.
Lemma lem1378204 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378206 : term34 = term34.
Proof. exact (MK_COMB (@lem1378204) (@lem1378203)). Qed.
Lemma lem1378207 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1378206) (@lem1378079 h1)). Qed.
Lemma lem1378231 (y : real) (x : real) : (term185 y x) = (term185 y x).
Proof. exact (eq_refl (term185 y x)). Qed.
Lemma lem1378232 (y : real) : (term200 y) = (term200 y).
Proof. exact (fun_ext (fun x : real => @lem1378231 y x)). Qed.
Lemma lem1378233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378234 (y : real) : (term215 y) = (term215 y).
Proof. exact (MK_COMB (@lem1378233) (@lem1378232 y)). Qed.
Lemma lem1378235 : term222 = term222.
Proof. exact (fun_ext (fun y : real => @lem1378234 y)). Qed.
Lemma lem1378236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378238 : term237 = term237.
Proof. exact (MK_COMB (@lem1378236) (@lem1378235)). Qed.
Lemma lem1378239 (h1 : term17) : term237.
Proof. exact (EQ_MP (@lem1378238) (@lem1378178 h1)). Qed.
Lemma lem1378295 (x : real) (y : real) (h1 : term26 x y) : term26 x y.
Proof. exact (h1). Qed.
Lemma lem1378335 (y : real) (x : real) : (term185 y x) = (term185 y x).
Proof. exact (eq_refl (term185 y x)). Qed.
Lemma lem1378336 (y : real) : (term200 y) = (term200 y).
Proof. exact (fun_ext (fun x : real => @lem1378335 y x)). Qed.
Lemma lem1378337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378338 (y : real) : (term215 y) = (term215 y).
Proof. exact (MK_COMB (@lem1378337) (@lem1378336 y)). Qed.
Lemma lem1378339 : term222 = term222.
Proof. exact (fun_ext (fun y : real => @lem1378338 y)). Qed.
Lemma lem1378340 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378342 : term237 = term237.
Proof. exact (MK_COMB (@lem1378340) (@lem1378339)). Qed.
Lemma lem1378343 (h1 : term17) : term237.
Proof. exact (EQ_MP (@lem1378342) (@lem1378178 h1)). Qed.
Lemma lem1378361 (x : real) (y : real) : (term146 x y) = (term239 x y).
Proof. exact (@lem19699 (real_le x y) (real_le y x) (term49 x y)). Qed.
Lemma lem1378362 (x : real) : (term143 x) = (term240 x).
Proof. exact (fun_ext (fun y : real => @lem1378361 x y)). Qed.
Lemma lem1378363 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378364 (x : real) : (term155 x) = (term241 x).
Proof. exact (MK_COMB (@lem1378363) (@lem1378362 x)). Qed.
Lemma lem1378365 : term166 = term242.
Proof. exact (fun_ext (fun x : real => @lem1378364 x)). Qed.
Lemma lem1378366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378368 : term177 = term243.
Proof. exact (MK_COMB (@lem1378366) (@lem1378365)). Qed.
Lemma lem1378369 (h1 : term39) : term243.
Proof. exact (EQ_MP (@lem1378368) (@lem1378181 h1)). Qed.
Lemma lem1378399 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1378423 (y : real) (x : real) : (term188 y x) = (term188 y x).
Proof. exact (eq_refl (term188 y x)). Qed.
Lemma lem1378424 (y : real) : (term199 y) = (term199 y).
Proof. exact (fun_ext (fun x : real => @lem1378423 y x)). Qed.
Lemma lem1378425 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378426 (y : real) : (term210 y) = (term210 y).
Proof. exact (MK_COMB (@lem1378425) (@lem1378424 y)). Qed.
Lemma lem1378427 : term221 = term221.
Proof. exact (fun_ext (fun y : real => @lem1378426 y)). Qed.
Lemma lem1378428 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378430 : term232 = term232.
Proof. exact (MK_COMB (@lem1378428) (@lem1378427)). Qed.
Lemma lem1378431 (h1 : term17) : term232.
Proof. exact (EQ_MP (@lem1378430) (@lem1378179 h1)). Qed.
Lemma lem1378487 (x : real) (y : real) : (term129 x y) = (term129 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1378488 (x : real) : (term144 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1378487 x y)). Qed.
Lemma lem1378489 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378490 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1378489) (@lem1378488 x)). Qed.
Lemma lem1378491 : term167 = term167.
Proof. exact (fun_ext (fun x : real => @lem1378490 x)). Qed.
Lemma lem1378492 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1378494 : term182 = term182.
Proof. exact (MK_COMB (@lem1378492) (@lem1378491)). Qed.
Lemma lem1378495 (h1 : term39) : term182.
Proof. exact (EQ_MP (@lem1378494) (@lem1378180 h1)). Qed.
Lemma lem1378508 (_24378 : real) (h1 : term34) : term244 _24378.
Proof. exact (@lem1378207 h1 _24378). Qed.
Lemma lem1378509 (_24378 : real) : (term244 _24378) = (term32 _24378).
Proof. exact (eq_refl (term244 _24378)). Qed.
Lemma lem1378510 (_24378 : real) (h1 : term34) : term32 _24378.
Proof. exact (EQ_MP (@lem1378509 _24378) (@lem1378508 _24378 h1)). Qed.
Lemma lem1378511 (_24378 : real) (_24379 : real) (h1 : term34) : term245 _24378 _24379.
Proof. exact (@lem1378510 _24378 h1 _24379). Qed.
Lemma lem1378512 (_24379 : real) (_24378 : real) : (term245 _24378 _24379) = (term30 _24379 _24378).
Proof. exact (eq_refl (term245 _24378 _24379)). Qed.
Lemma lem1378520 (_24382 : real) (h1 : term17) : term225 _24382.
Proof. exact (@lem1378239 h1 _24382). Qed.
Lemma lem1378521 (_24382 : real) : (term225 _24382) = (term215 _24382).
Proof. exact (eq_refl (term225 _24382)). Qed.
Lemma lem1378522 (_24382 : real) (h1 : term17) : term215 _24382.
Proof. exact (EQ_MP (@lem1378521 _24382) (@lem1378520 _24382 h1)). Qed.
Lemma lem1378523 (_24382 : real) (_24383 : real) (h1 : term17) : term203 _24382 _24383.
Proof. exact (@lem1378522 _24382 h1 _24383). Qed.
Lemma lem1378524 (_24382 : real) (_24383 : real) : (term203 _24382 _24383) = (term185 _24382 _24383).
Proof. exact (eq_refl (term203 _24382 _24383)). Qed.
Lemma lem1378550 (_24392 : real) (h1 : term17) : term225 _24392.
Proof. exact (@lem1378343 h1 _24392). Qed.
Lemma lem1378551 (_24392 : real) : (term225 _24392) = (term215 _24392).
Proof. exact (eq_refl (term225 _24392)). Qed.
Lemma lem1378552 (_24392 : real) (h1 : term17) : term215 _24392.
Proof. exact (EQ_MP (@lem1378551 _24392) (@lem1378550 _24392 h1)). Qed.
Lemma lem1378553 (_24392 : real) (_24393 : real) (h1 : term17) : term203 _24392 _24393.
Proof. exact (@lem1378552 _24392 h1 _24393). Qed.
Lemma lem1378554 (_24392 : real) (_24393 : real) : (term203 _24392 _24393) = (term185 _24392 _24393).
Proof. exact (eq_refl (term203 _24392 _24393)). Qed.
Lemma lem1378556 (_24394 : real) (h1 : term39) : term246 _24394.
Proof. exact (@lem1378369 h1 _24394). Qed.
Lemma lem1378557 (_24394 : real) : (term246 _24394) = (term241 _24394).
Proof. exact (eq_refl (term246 _24394)). Qed.
Lemma lem1378558 (_24394 : real) (h1 : term39) : term241 _24394.
Proof. exact (EQ_MP (@lem1378557 _24394) (@lem1378556 _24394 h1)). Qed.
Lemma lem1378559 (_24394 : real) (_24395 : real) (h1 : term39) : term247 _24394 _24395.
Proof. exact (@lem1378558 _24394 h1 _24395). Qed.
Lemma lem1378560 (_24394 : real) (_24395 : real) : (term247 _24394 _24395) = (term239 _24394 _24395).
Proof. exact (eq_refl (term247 _24394 _24395)). Qed.
Lemma lem1378561 (_24394 : real) (_24395 : real) (h1 : term39) : term239 _24394 _24395.
Proof. exact (EQ_MP (@lem1378560 _24394 _24395) (@lem1378559 _24394 _24395 h1)). Qed.
Lemma lem1378574 (_24400 : real) (h1 : term17) : term223 _24400.
Proof. exact (@lem1378431 h1 _24400). Qed.
Lemma lem1378575 (_24400 : real) : (term223 _24400) = (term210 _24400).
Proof. exact (eq_refl (term223 _24400)). Qed.
Lemma lem1378576 (_24400 : real) (h1 : term17) : term210 _24400.
Proof. exact (EQ_MP (@lem1378575 _24400) (@lem1378574 _24400 h1)). Qed.
Lemma lem1378577 (_24400 : real) (_24401 : real) (h1 : term17) : term201 _24400 _24401.
Proof. exact (@lem1378576 _24400 h1 _24401). Qed.
Lemma lem1378578 (_24400 : real) (_24401 : real) : (term201 _24400 _24401) = (term188 _24400 _24401).
Proof. exact (eq_refl (term201 _24400 _24401)). Qed.
Lemma lem1378592 (_24406 : real) (h1 : term39) : term170 _24406.
Proof. exact (@lem1378495 h1 _24406). Qed.
Lemma lem1378593 (_24406 : real) : (term170 _24406) = (term160 _24406).
Proof. exact (eq_refl (term170 _24406)). Qed.
Lemma lem1378594 (_24406 : real) (h1 : term39) : term160 _24406.
Proof. exact (EQ_MP (@lem1378593 _24406) (@lem1378592 _24406 h1)). Qed.
Lemma lem1378595 (_24406 : real) (_24407 : real) (h1 : term39) : term148 _24406 _24407.
Proof. exact (@lem1378594 _24406 h1 _24407). Qed.
Lemma lem1378596 (_24406 : real) (_24407 : real) : (term148 _24406 _24407) = (term129 _24406 _24407).
Proof. exact (eq_refl (term148 _24406 _24407)). Qed.
Lemma lem1378597 (_24406 : real) (_24407 : real) (h1 : term39) : term129 _24406 _24407.
Proof. exact (EQ_MP (@lem1378596 _24406 _24407) (@lem1378595 _24406 _24407 h1)). Qed.
Lemma lem1378609 (_24379 : real) (_24378 : real) (h1 : term34) : term30 _24379 _24378.
Proof. exact (EQ_MP (@lem1378512 _24379 _24378) (@lem1378511 _24378 _24379 h1)). Qed.
Lemma lem1378621 (_24382 : real) (_24383 : real) (h1 : term17) : term185 _24382 _24383.
Proof. exact (EQ_MP (@lem1378524 _24382 _24383) (@lem1378523 _24382 _24383 h1)). Qed.
Lemma lem1378637 (x : real) (y : real) (h1 : term26 x y) : term26 x y.
Proof. exact (h1). Qed.
Lemma lem1378681 (x : real) (y : real) (h1 : term53 x y) : real_lt x y.
Proof. exact (proj1 (@lem1378182 x y h1)). Qed.
Lemma lem1378683 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1378707 (_24400 : real) (_24401 : real) (h1 : term17) : term188 _24400 _24401.
Proof. exact (EQ_MP (@lem1378578 _24400 _24401) (@lem1378577 _24400 _24401 h1)). Qed.
Lemma lem1378724 (_24406 : real) (_24407 : real) : (term129 _24406 _24407) = (term248 _24406 _24407).
Proof. exact (@lem1376705 (term26 _24406 _24407) (term26 _24407 _24406) (_24406 = _24407)). Qed.
Lemma lem1378725 (_24406 : real) (_24407 : real) (h1 : term39) : term248 _24406 _24407.
Proof. exact (EQ_MP (@lem1378724 _24406 _24407) (@lem1378597 _24406 _24407 h1)). Qed.
Lemma lem1378731 (x : real) (y : real) (h1 : term50 x y) : term49 x y.
Proof. exact (proj2 (@lem1378188 x y h1)). Qed.
Lemma lem1378799 (_24392 : real) (_24393 : real) (h1 : term17) : term185 _24392 _24393.
Proof. exact (EQ_MP (@lem1378554 _24392 _24393) (@lem1378553 _24392 _24393 h1)). Qed.
Lemma lem1378814 (y : real) : (term249 y) = (term249 y).
Proof. exact (eq_refl (term249 y)). Qed.
Lemma lem1378815 (x : real) (y : real) (h1 : x = y) : (term250 y x) = (term251 y).
Proof. exact (MK_COMB (@lem1378814 y) (@lem1378683 x y h1)). Qed.
Lemma lem1378816 (y : real) : (term251 y) = (real_lt y y).
Proof. exact (eq_refl (term251 y)). Qed.
Lemma lem1378817 (y : real) (x : real) : (term252 y x) = (term252 y x).
Proof. exact (eq_refl (term252 y x)). Qed.
Lemma lem1378818 (x : real) (y : real) : ((term250 y x) = (term251 y)) = ((term250 y x) = (real_lt y y)).
Proof. exact (MK_COMB (@lem1378817 y x) (@lem1378816 y)). Qed.
Lemma lem1378819 (x : real) (y : real) : (term250 y x) = (real_lt x y).
Proof. exact (eq_refl (term250 y x)). Qed.
Lemma lem1378820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1378821 (x : real) (y : real) : (term252 y x) = (term253 x y).
Proof. exact (MK_COMB (@lem1378820) (@lem1378819 x y)). Qed.
Lemma lem1378822 (y : real) : (real_lt y y) = (real_lt y y).
Proof. exact (eq_refl (real_lt y y)). Qed.
Lemma lem1378823 (x : real) (y : real) : ((term250 y x) = (real_lt y y)) = ((real_lt x y) = (real_lt y y)).
Proof. exact (MK_COMB (@lem1378821 x y) (@lem1378822 y)). Qed.
Lemma lem1378824 (x : real) (y : real) : ((term250 y x) = (term251 y)) = ((real_lt x y) = (real_lt y y)).
Proof. exact (TRANS (@lem1378818 x y) (@lem1378823 x y)). Qed.
Lemma lem1378825 (x : real) (y : real) (h1 : x = y) : (real_lt x y) = (real_lt y y).
Proof. exact (EQ_MP (@lem1378824 x y) (@lem1378815 x y h1)). Qed.
Lemma lem1378854 (_24394 : real) (_24395 : real) (h1 : term39) : term254 _24394 _24395.
Proof. exact (proj2 (@lem1378561 _24394 _24395 h1)). Qed.
Lemma lem1378896 (x : real) (y : real) (h1 : term53 x y) : real_lt x y.
Proof. exact (proj1 (@lem1378182 x y h1)). Qed.
Lemma lem1378897 (x : real) (y : real) (h1 : term53 x y) : term255 x y.
Proof. exact (fun h0 : term256 x y => @lem1378896 x y h1). Qed.
Lemma lem1378899 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1378900 (x : real) (y : real) : (term255 x y) = (real_lt x y).
Proof. exact (@lem1378899 (real_lt x y)). Qed.
Lemma lem1378901 (x : real) (y : real) (h1 : term53 x y) : real_lt x y.
Proof. exact (EQ_MP (@lem1378900 x y) (@lem1378897 x y h1)). Qed.
Lemma lem1378907 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1378908 (_24383 : real) (_24382 : real) : (term185 _24382 _24383) = (term258 _24383 _24382).
Proof. exact (@lem1378907 (term26 _24382 _24383) (term256 _24383 _24382)). Qed.
Lemma lem1378914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1378915 (_24383 : real) (_24382 : real) : (term259 _24382 _24383) = (term260 _24383 _24382).
Proof. exact (MK_COMB (@lem1378914) (@lem1378908 _24383 _24382)). Qed.
Lemma lem1378921 (_24383 : real) (_24382 : real) : (term258 _24383 _24382) = (term258 _24383 _24382).
Proof. exact (eq_refl (term258 _24383 _24382)). Qed.
Lemma lem1378922 (_24383 : real) (_24382 : real) : ((term185 _24382 _24383) = (term258 _24383 _24382)) = ((term258 _24383 _24382) = (term258 _24383 _24382)).
Proof. exact (MK_COMB (@lem1378915 _24383 _24382) (@lem1378921 _24383 _24382)). Qed.
Lemma lem1378924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1378925 (x : Prop) : (x = x) = True.
Proof. exact (@lem1378924 Prop x). Qed.
Lemma lem1378926 (_24383 : real) (_24382 : real) : ((term258 _24383 _24382) = (term258 _24383 _24382)) = True.
Proof. exact (@lem1378925 (term258 _24383 _24382)). Qed.
Lemma lem1378927 (_24383 : real) (_24382 : real) : ((term185 _24382 _24383) = (term258 _24383 _24382)) = True.
Proof. exact (TRANS (@lem1378922 _24383 _24382) (@lem1378926 _24383 _24382)). Qed.
Lemma lem1378928 (_24383 : real) (_24382 : real) : True = ((term185 _24382 _24383) = (term258 _24383 _24382)).
Proof. exact (SYM (@lem1378927 _24383 _24382)). Qed.
Lemma lem1378929 (_24383 : real) (_24382 : real) : (term185 _24382 _24383) = (term258 _24383 _24382).
Proof. exact (EQ_MP (@lem1378928 _24383 _24382) (@lem0)). Qed.
Lemma lem1378930 (_24383 : real) (_24382 : real) (h1 : term17) : term258 _24383 _24382.
Proof. exact (EQ_MP (@lem1378929 _24383 _24382) (@lem1378621 _24382 _24383 h1)). Qed.
Lemma lem1378932 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1378933 (_24382 : real) (_24383 : real) : (term258 _24383 _24382) = (term262 _24382 _24383).
Proof. exact (@lem1378932 (term256 _24383 _24382) (term26 _24382 _24383)). Qed.
Lemma lem1378935 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1378936 (_24383 : real) (_24382 : real) : (term264 _24383 _24382) = (real_lt _24383 _24382).
Proof. exact (@lem1378935 (real_lt _24383 _24382)). Qed.
Lemma lem1378937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1378938 (_24383 : real) (_24382 : real) : (term265 _24383 _24382) = (term266 _24383 _24382).
Proof. exact (MK_COMB (@lem1378937) (@lem1378936 _24383 _24382)). Qed.
Lemma lem1378939 (_24382 : real) (_24383 : real) : (term26 _24382 _24383) = (term26 _24382 _24383).
Proof. exact (eq_refl (term26 _24382 _24383)). Qed.
Lemma lem1378940 (_24382 : real) (_24383 : real) : (term262 _24382 _24383) = (term267 _24382 _24383).
Proof. exact (MK_COMB (@lem1378938 _24383 _24382) (@lem1378939 _24382 _24383)). Qed.
Lemma lem1378941 (_24382 : real) (_24383 : real) : (term258 _24383 _24382) = (term267 _24382 _24383).
Proof. exact (TRANS (@lem1378933 _24382 _24383) (@lem1378940 _24382 _24383)). Qed.
Lemma lem1378944 (_24382 : real) (_24383 : real) (h1 : term17) : term267 _24382 _24383.
Proof. exact (EQ_MP (@lem1378941 _24382 _24383) (@lem1378930 _24383 _24382 h1)). Qed.
Lemma lem1378945 (y : real) (x : real) (h1 : term17) : term267 y x.
Proof. exact (@lem1378944 y x h1). Qed.
Lemma lem1378948 (x : real) (y : real) (h1 : term17) (h2 : term53 x y) : term26 y x.
Proof. exact (@lem1378945 y x h1 (@lem1378901 x y h2)). Qed.
Lemma lem1378949 (x : real) (y : real) (h1 : term17) (h2 : term53 x y) : term268 y x.
Proof. exact (fun h0 : real_le y x => @lem1378948 x y h1 h2). Qed.
Lemma lem1378951 (p : Prop) : (term269 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1378952 (y : real) (x : real) : (term268 y x) = (term26 y x).
Proof. exact (@lem1378951 (real_le y x)). Qed.
Lemma lem1378953 (x : real) (y : real) (h1 : term17) (h2 : term53 x y) : term26 y x.
Proof. exact (EQ_MP (@lem1378952 y x) (@lem1378949 x y h1 h2)). Qed.
Lemma lem1378964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1378965 (_24379 : real) (_24378 : real) : (term30 _24378 _24379) = (term30 _24379 _24378).
Proof. exact (@lem1378964 (real_le _24378 _24379) (real_le _24379 _24378)). Qed.
Lemma lem1378971 (_24379 : real) (_24378 : real) : (term270 _24379 _24378) = (term270 _24379 _24378).
Proof. exact (eq_refl (term270 _24379 _24378)). Qed.
Lemma lem1378972 (_24379 : real) (_24378 : real) : ((term30 _24379 _24378) = (term30 _24378 _24379)) = ((term30 _24379 _24378) = (term30 _24379 _24378)).
Proof. exact (MK_COMB (@lem1378971 _24379 _24378) (@lem1378965 _24379 _24378)). Qed.
Lemma lem1378974 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1378975 (x : Prop) : (x = x) = True.
Proof. exact (@lem1378974 Prop x). Qed.
Lemma lem1378976 (_24379 : real) (_24378 : real) : ((term30 _24379 _24378) = (term30 _24379 _24378)) = True.
Proof. exact (@lem1378975 (term30 _24379 _24378)). Qed.
Lemma lem1378977 (_24378 : real) (_24379 : real) : ((term30 _24379 _24378) = (term30 _24378 _24379)) = True.
Proof. exact (TRANS (@lem1378972 _24379 _24378) (@lem1378976 _24379 _24378)). Qed.
Lemma lem1378978 (_24378 : real) (_24379 : real) : True = ((term30 _24379 _24378) = (term30 _24378 _24379)).
Proof. exact (SYM (@lem1378977 _24378 _24379)). Qed.
Lemma lem1378979 (_24378 : real) (_24379 : real) : (term30 _24379 _24378) = (term30 _24378 _24379).
Proof. exact (EQ_MP (@lem1378978 _24378 _24379) (@lem0)). Qed.
Lemma lem1378980 (_24378 : real) (_24379 : real) (h1 : term34) : term30 _24378 _24379.
Proof. exact (EQ_MP (@lem1378979 _24378 _24379) (@lem1378609 _24379 _24378 h1)). Qed.
Lemma lem1378982 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1378985 (_24379 : real) (_24378 : real) : (term30 _24378 _24379) = (term271 _24379 _24378).
Proof. exact (@lem1378982 (real_le _24378 _24379) (real_le _24379 _24378)). Qed.
Lemma lem1378988 (_24379 : real) (_24378 : real) (h1 : term34) : term271 _24379 _24378.
Proof. exact (EQ_MP (@lem1378985 _24379 _24378) (@lem1378980 _24378 _24379 h1)). Qed.
Lemma lem1378989 (x : real) (y : real) (h1 : term34) : term271 x y.
Proof. exact (@lem1378988 x y h1). Qed.
Lemma lem1378992 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term53 x y) : real_le x y.
Proof. exact (@lem1378989 x y h2 (@lem1378953 x y h1 h3)). Qed.
Lemma lem1378993 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term53 x y) : term272 x y.
Proof. exact (fun h0 : term26 x y => @lem1378992 x y h1 h2 h3). Qed.
Lemma lem1378995 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1378996 (x : real) (y : real) : (term272 x y) = (real_le x y).
Proof. exact (@lem1378995 (real_le x y)). Qed.
Lemma lem1378997 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term53 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1378996 x y) (@lem1378993 x y h1 h2 h3)). Qed.
Lemma lem1379000 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1379002 (x : real) (y : real) : (term26 x y) = (term273 x y).
Proof. exact (@lem1379000 (real_le x y)). Qed.
Lemma lem1379005 (x : real) (y : real) (h1 : term26 x y) : term273 x y.
Proof. exact (EQ_MP (@lem1379002 x y) (@lem1378637 x y h1)). Qed.
Lemma lem1379008 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : False.
Proof. exact (@lem1379005 x y h3 (@lem1378997 x y h1 h2 h4)). Qed.
Lemma lem1379009 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : term274.
Proof. exact (fun h0 : ~ False => @lem1379008 x y h1 h2 h3 h4). Qed.
Lemma lem1379011 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379012 : term274 = False.
Proof. exact (@lem1379011 False). Qed.
Lemma lem1379013 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1379012) (@lem1379009 x y h1 h2 h3 h4)). Qed.
Lemma lem1379055 (x : real) (y : real) (h1 : term53 x y) (h2 : x = y) : real_lt y y.
Proof. exact (EQ_MP (@lem1378825 x y h2) (@lem1378681 x y h1)). Qed.
Lemma lem1379056 (x : real) (y : real) (h1 : term53 x y) (h2 : x = y) : term275 y.
Proof. exact (fun h0 : term276 y => @lem1379055 x y h1 h2). Qed.
Lemma lem1379058 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379059 (y : real) : (term275 y) = (real_lt y y).
Proof. exact (@lem1379058 (real_lt y y)). Qed.
Lemma lem1379060 (x : real) (y : real) (h1 : term53 x y) (h2 : x = y) : real_lt y y.
Proof. exact (EQ_MP (@lem1379059 y) (@lem1379056 x y h1 h2)). Qed.
Lemma lem1379062 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1379063 (y : real) : y = y.
Proof. exact (@lem1379062 y). Qed.
Lemma lem1379064 (y : real) : term277 y.
Proof. exact (fun h0 : term278 y => @lem1379063 y). Qed.
Lemma lem1379066 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379067 (y : real) : (term277 y) = (y = y).
Proof. exact (@lem1379066 (y = y)). Qed.
Lemma lem1379068 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1379067 y) (@lem1379064 y)). Qed.
Lemma lem1379070 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1379071 (_24395 : real) (_24394 : real) : (term254 _24394 _24395) = (term279 _24395 _24394).
Proof. exact (@lem1379070 (term49 _24394 _24395) (real_le _24395 _24394)). Qed.
Lemma lem1379073 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1379074 (_24394 : real) (_24395 : real) : (term44 _24394 _24395) = (_24394 = _24395).
Proof. exact (@lem1379073 (_24394 = _24395)). Qed.
Lemma lem1379075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1379076 (_24394 : real) (_24395 : real) : (term280 _24394 _24395) = (term281 _24394 _24395).
Proof. exact (MK_COMB (@lem1379075) (@lem1379074 _24394 _24395)). Qed.
Lemma lem1379077 (_24395 : real) (_24394 : real) : (real_le _24395 _24394) = (real_le _24395 _24394).
Proof. exact (eq_refl (real_le _24395 _24394)). Qed.
Lemma lem1379078 (_24395 : real) (_24394 : real) : (term279 _24395 _24394) = (term282 _24395 _24394).
Proof. exact (MK_COMB (@lem1379076 _24394 _24395) (@lem1379077 _24395 _24394)). Qed.
Lemma lem1379079 (_24395 : real) (_24394 : real) : (term254 _24394 _24395) = (term282 _24395 _24394).
Proof. exact (TRANS (@lem1379071 _24395 _24394) (@lem1379078 _24395 _24394)). Qed.
Lemma lem1379082 (_24395 : real) (_24394 : real) (h1 : term39) : term282 _24395 _24394.
Proof. exact (EQ_MP (@lem1379079 _24395 _24394) (@lem1378854 _24394 _24395 h1)). Qed.
Lemma lem1379083 (y : real) (h1 : term39) : term283 y.
Proof. exact (@lem1379082 y y h1). Qed.
Lemma lem1379086 (y : real) (h1 : term39) : real_le y y.
Proof. exact (@lem1379083 y h1 (@lem1379068 y)). Qed.
Lemma lem1379087 (y : real) (h1 : term39) : term284 y.
Proof. exact (fun h0 : term285 y => @lem1379086 y h1). Qed.
Lemma lem1379089 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379090 (y : real) : (term284 y) = (real_le y y).
Proof. exact (@lem1379089 (real_le y y)). Qed.
Lemma lem1379091 (y : real) (h1 : term39) : real_le y y.
Proof. exact (EQ_MP (@lem1379090 y) (@lem1379087 y h1)). Qed.
Lemma lem1379093 (a : Prop) (b : Prop) : (term286 a b) = (term287 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1379094 (_24392 : real) (_24393 : real) : (term185 _24392 _24393) = (term288 _24392 _24393).
Proof. exact (@lem1379093 (real_lt _24393 _24392) (real_le _24392 _24393)). Qed.
Lemma lem1379096 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1379097 (_24392 : real) (_24393 : real) : (term288 _24392 _24393) = (term289 _24392 _24393).
Proof. exact (@lem1379096 (term290 _24392 _24393)). Qed.
Lemma lem1379098 (_24392 : real) (_24393 : real) : (term185 _24392 _24393) = (term289 _24392 _24393).
Proof. exact (TRANS (@lem1379094 _24392 _24393) (@lem1379097 _24392 _24393)). Qed.
Lemma lem1379100 (x : real) (y : real) (h1 : term39) (h2 : term53 x y) (h3 : x = y) : term291 y.
Proof. exact (conj (@lem1379060 x y h2 h3) (@lem1379091 y h1)). Qed.
Lemma lem1379102 (_24392 : real) (_24393 : real) (h1 : term17) : term289 _24392 _24393.
Proof. exact (EQ_MP (@lem1379098 _24392 _24393) (@lem1378799 _24392 _24393 h1)). Qed.
Lemma lem1379103 (y : real) (h1 : term17) : term292 y.
Proof. exact (@lem1379102 y y h1). Qed.
Lemma lem1379106 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : False.
Proof. exact (@lem1379103 y h2 (@lem1379100 x y h1 h3 h4)). Qed.
Lemma lem1379107 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : term274.
Proof. exact (fun h0 : ~ False => @lem1379106 x y h1 h2 h3 h4). Qed.
Lemma lem1379109 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379110 : term274 = False.
Proof. exact (@lem1379109 False). Qed.
Lemma lem1379153 (x : real) (y : real) (h1 : term50 x y) : real_le x y.
Proof. exact (proj1 (@lem1378188 x y h1)). Qed.
Lemma lem1379154 (x : real) (y : real) (h1 : term50 x y) : term272 x y.
Proof. exact (fun h0 : term26 x y => @lem1379153 x y h1). Qed.
Lemma lem1379156 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379157 (x : real) (y : real) : (term272 x y) = (real_le x y).
Proof. exact (@lem1379156 (real_le x y)). Qed.
Lemma lem1379158 (x : real) (y : real) (h1 : term50 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1379157 x y) (@lem1379154 x y h1)). Qed.
Lemma lem1379160 (x : real) (y : real) (h1 : term50 x y) : term256 x y.
Proof. exact (proj1 (@lem1378183 x y h1)). Qed.
Lemma lem1379161 (x : real) (y : real) (h1 : term50 x y) : term293 x y.
Proof. exact (fun h0 : real_lt x y => @lem1379160 x y h1). Qed.
Lemma lem1379163 (p : Prop) : (term269 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1379164 (x : real) (y : real) : (term293 x y) = (term256 x y).
Proof. exact (@lem1379163 (real_lt x y)). Qed.
Lemma lem1379165 (x : real) (y : real) (h1 : term50 x y) : term256 x y.
Proof. exact (EQ_MP (@lem1379164 x y) (@lem1379161 x y h1)). Qed.
Lemma lem1379171 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1379172 (_24401 : real) (_24400 : real) : (term188 _24400 _24401) = (term294 _24401 _24400).
Proof. exact (@lem1379171 (real_le _24400 _24401) (real_lt _24401 _24400)). Qed.
Lemma lem1379178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1379179 (_24401 : real) (_24400 : real) : (term295 _24400 _24401) = (term296 _24401 _24400).
Proof. exact (MK_COMB (@lem1379178) (@lem1379172 _24401 _24400)). Qed.
Lemma lem1379185 (_24401 : real) (_24400 : real) : (term294 _24401 _24400) = (term294 _24401 _24400).
Proof. exact (eq_refl (term294 _24401 _24400)). Qed.
Lemma lem1379186 (_24401 : real) (_24400 : real) : ((term188 _24400 _24401) = (term294 _24401 _24400)) = ((term294 _24401 _24400) = (term294 _24401 _24400)).
Proof. exact (MK_COMB (@lem1379179 _24401 _24400) (@lem1379185 _24401 _24400)). Qed.
Lemma lem1379188 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1379189 (x : Prop) : (x = x) = True.
Proof. exact (@lem1379188 Prop x). Qed.
Lemma lem1379190 (_24401 : real) (_24400 : real) : ((term294 _24401 _24400) = (term294 _24401 _24400)) = True.
Proof. exact (@lem1379189 (term294 _24401 _24400)). Qed.
Lemma lem1379191 (_24401 : real) (_24400 : real) : ((term188 _24400 _24401) = (term294 _24401 _24400)) = True.
Proof. exact (TRANS (@lem1379186 _24401 _24400) (@lem1379190 _24401 _24400)). Qed.
Lemma lem1379192 (_24401 : real) (_24400 : real) : True = ((term188 _24400 _24401) = (term294 _24401 _24400)).
Proof. exact (SYM (@lem1379191 _24401 _24400)). Qed.
Lemma lem1379193 (_24401 : real) (_24400 : real) : (term188 _24400 _24401) = (term294 _24401 _24400).
Proof. exact (EQ_MP (@lem1379192 _24401 _24400) (@lem0)). Qed.
Lemma lem1379194 (_24401 : real) (_24400 : real) (h1 : term17) : term294 _24401 _24400.
Proof. exact (EQ_MP (@lem1379193 _24401 _24400) (@lem1378707 _24400 _24401 h1)). Qed.
Lemma lem1379196 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1379199 (_24400 : real) (_24401 : real) : (term294 _24401 _24400) = (term297 _24400 _24401).
Proof. exact (@lem1379196 (real_lt _24401 _24400) (real_le _24400 _24401)). Qed.
Lemma lem1379202 (_24400 : real) (_24401 : real) (h1 : term17) : term297 _24400 _24401.
Proof. exact (EQ_MP (@lem1379199 _24400 _24401) (@lem1379194 _24401 _24400 h1)). Qed.
Lemma lem1379203 (y : real) (x : real) (h1 : term17) : term297 y x.
Proof. exact (@lem1379202 y x h1). Qed.
Lemma lem1379206 (x : real) (y : real) (h1 : term17) (h2 : term50 x y) : real_le y x.
Proof. exact (@lem1379203 y x h1 (@lem1379165 x y h2)). Qed.
Lemma lem1379207 (x : real) (y : real) (h1 : term17) (h2 : term50 x y) : term272 y x.
Proof. exact (fun h0 : term26 y x => @lem1379206 x y h1 h2). Qed.
Lemma lem1379209 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379210 (y : real) (x : real) : (term272 y x) = (real_le y x).
Proof. exact (@lem1379209 (real_le y x)). Qed.
Lemma lem1379211 (x : real) (y : real) (h1 : term17) (h2 : term50 x y) : real_le y x.
Proof. exact (EQ_MP (@lem1379210 y x) (@lem1379207 x y h1 h2)). Qed.
Lemma lem1379227 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1379228 (_24407 : real) (_24406 : real) : (term298 _24406 _24407) = (term299 _24407 _24406).
Proof. exact (@lem1379227 (_24406 = _24407) (term26 _24407 _24406)). Qed.
Lemma lem1379236 (_24406 : real) (_24407 : real) : (term45 _24406 _24407) = (term45 _24406 _24407).
Proof. exact (eq_refl (term45 _24406 _24407)). Qed.
Lemma lem1379237 (_24407 : real) (_24406 : real) : (term248 _24406 _24407) = (term300 _24407 _24406).
Proof. exact (MK_COMB (@lem1379236 _24406 _24407) (@lem1379228 _24407 _24406)). Qed.
Lemma lem1379241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1379242 (_24407 : real) (_24406 : real) : (term300 _24407 _24406) = (term301 _24407 _24406).
Proof. exact (@lem1379241 (_24406 = _24407) (term26 _24406 _24407) (term26 _24407 _24406)). Qed.
Lemma lem1379260 (_24407 : real) (_24406 : real) : (term248 _24406 _24407) = (term301 _24407 _24406).
Proof. exact (TRANS (@lem1379237 _24407 _24406) (@lem1379242 _24407 _24406)). Qed.
Lemma lem1379261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1379262 (_24407 : real) (_24406 : real) : (term302 _24406 _24407) = (term303 _24407 _24406).
Proof. exact (MK_COMB (@lem1379261) (@lem1379260 _24407 _24406)). Qed.
Lemma lem1379280 (_24407 : real) (_24406 : real) : (term301 _24407 _24406) = (term301 _24407 _24406).
Proof. exact (eq_refl (term301 _24407 _24406)). Qed.
Lemma lem1379281 (_24407 : real) (_24406 : real) : ((term248 _24406 _24407) = (term301 _24407 _24406)) = ((term301 _24407 _24406) = (term301 _24407 _24406)).
Proof. exact (MK_COMB (@lem1379262 _24407 _24406) (@lem1379280 _24407 _24406)). Qed.
Lemma lem1379283 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1379284 (x : Prop) : (x = x) = True.
Proof. exact (@lem1379283 Prop x). Qed.
Lemma lem1379285 (_24407 : real) (_24406 : real) : ((term301 _24407 _24406) = (term301 _24407 _24406)) = True.
Proof. exact (@lem1379284 (term301 _24407 _24406)). Qed.
Lemma lem1379286 (_24407 : real) (_24406 : real) : ((term248 _24406 _24407) = (term301 _24407 _24406)) = True.
Proof. exact (TRANS (@lem1379281 _24407 _24406) (@lem1379285 _24407 _24406)). Qed.
Lemma lem1379287 (_24407 : real) (_24406 : real) : True = ((term248 _24406 _24407) = (term301 _24407 _24406)).
Proof. exact (SYM (@lem1379286 _24407 _24406)). Qed.
Lemma lem1379288 (_24407 : real) (_24406 : real) : (term248 _24406 _24407) = (term301 _24407 _24406).
Proof. exact (EQ_MP (@lem1379287 _24407 _24406) (@lem0)). Qed.
Lemma lem1379289 (_24407 : real) (_24406 : real) (h1 : term39) : term301 _24407 _24406.
Proof. exact (EQ_MP (@lem1379288 _24407 _24406) (@lem1378725 _24406 _24407 h1)). Qed.
Lemma lem1379291 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1379292 (_24406 : real) (_24407 : real) : (term301 _24407 _24406) = (term304 _24406 _24407).
Proof. exact (@lem1379291 (term125 _24407 _24406) (_24406 = _24407)). Qed.
Lemma lem1379294 (a : Prop) (b : Prop) : (term305 a b) = (term306 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1379295 (_24407 : real) (_24406 : real) : (term307 _24407 _24406) = (term308 _24407 _24406).
Proof. exact (@lem1379294 (term26 _24406 _24407) (term26 _24407 _24406)). Qed.
Lemma lem1379297 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1379298 (_24406 : real) (_24407 : real) : (term184 _24406 _24407) = (real_le _24406 _24407).
Proof. exact (@lem1379297 (real_le _24406 _24407)). Qed.
Lemma lem1379299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1379300 (_24406 : real) (_24407 : real) : (term309 _24406 _24407) = (term310 _24406 _24407).
Proof. exact (MK_COMB (@lem1379299) (@lem1379298 _24406 _24407)). Qed.
Lemma lem1379302 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1379303 (_24407 : real) (_24406 : real) : (term184 _24407 _24406) = (real_le _24407 _24406).
Proof. exact (@lem1379302 (real_le _24407 _24406)). Qed.
Lemma lem1379304 (_24407 : real) (_24406 : real) : (term308 _24407 _24406) = (term35 _24407 _24406).
Proof. exact (MK_COMB (@lem1379300 _24406 _24407) (@lem1379303 _24407 _24406)). Qed.
Lemma lem1379305 (_24407 : real) (_24406 : real) : (term307 _24407 _24406) = (term35 _24407 _24406).
Proof. exact (TRANS (@lem1379295 _24407 _24406) (@lem1379304 _24407 _24406)). Qed.
Lemma lem1379306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1379307 (_24407 : real) (_24406 : real) : (term311 _24407 _24406) = (term312 _24407 _24406).
Proof. exact (MK_COMB (@lem1379306) (@lem1379305 _24407 _24406)). Qed.
Lemma lem1379308 (_24406 : real) (_24407 : real) : (_24406 = _24407) = (_24406 = _24407).
Proof. exact (eq_refl (_24406 = _24407)). Qed.
Lemma lem1379309 (_24406 : real) (_24407 : real) : (term304 _24406 _24407) = (term313 _24406 _24407).
Proof. exact (MK_COMB (@lem1379307 _24407 _24406) (@lem1379308 _24406 _24407)). Qed.
Lemma lem1379310 (_24406 : real) (_24407 : real) : (term301 _24407 _24406) = (term313 _24406 _24407).
Proof. exact (TRANS (@lem1379292 _24406 _24407) (@lem1379309 _24406 _24407)). Qed.
Lemma lem1379312 (x : real) (y : real) (h1 : term17) (h2 : term50 x y) : term35 y x.
Proof. exact (conj (@lem1379158 x y h2) (@lem1379211 x y h1 h2)). Qed.
Lemma lem1379314 (_24406 : real) (_24407 : real) (h1 : term39) : term313 _24406 _24407.
Proof. exact (EQ_MP (@lem1379310 _24406 _24407) (@lem1379289 _24407 _24406 h1)). Qed.
Lemma lem1379315 (x : real) (y : real) (h1 : term39) : term313 x y.
Proof. exact (@lem1379314 x y h1). Qed.
Lemma lem1379318 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term50 x y) : x = y.
Proof. exact (@lem1379315 x y h1 (@lem1379312 x y h2 h3)). Qed.
Lemma lem1379319 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term50 x y) : term314 x y.
Proof. exact (fun h0 : term49 x y => @lem1379318 x y h1 h2 h3). Qed.
Lemma lem1379321 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379322 (x : real) (y : real) : (term314 x y) = (x = y).
Proof. exact (@lem1379321 (x = y)). Qed.
Lemma lem1379323 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term50 x y) : x = y.
Proof. exact (EQ_MP (@lem1379322 x y) (@lem1379319 x y h1 h2 h3)). Qed.
Lemma lem1379326 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1379328 (x : real) (y : real) : (term49 x y) = (term315 x y).
Proof. exact (@lem1379326 (x = y)). Qed.
Lemma lem1379331 (x : real) (y : real) (h1 : term50 x y) : term315 x y.
Proof. exact (EQ_MP (@lem1379328 x y) (@lem1378731 x y h1)). Qed.
Lemma lem1379334 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term50 x y) : False.
Proof. exact (@lem1379331 x y h3 (@lem1379323 x y h1 h2 h3)). Qed.
Lemma lem1379335 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term50 x y) : term274.
Proof. exact (fun h0 : ~ False => @lem1379334 x y h1 h2 h3). Qed.
Lemma lem1379337 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1379338 : term274 = False.
Proof. exact (@lem1379337 False). Qed.
Lemma lem1379339 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term50 x y) : False.
Proof. exact (EQ_MP (@lem1379338) (@lem1379335 x y h1 h2 h3)). Qed.
Lemma lem1379340 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1379110) (@lem1379107 x y h1 h2 h3 h4)). Qed.
Lemma lem1379341 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1379340 x y h1 h2 h3 h4) (fun h5 : False => @lem1378683 x y h4)). Qed.
Lemma lem1379342 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1379341 x y h1 h2 h3 h4) (@lem1378683 x y h4)). Qed.
Lemma lem1379343 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : (term26 x y) = False.
Proof. exact (prop_ext (fun h5 : term26 x y => @lem1379013 x y h1 h2 h3 h4) (fun h5 : False => @lem1378637 x y h3)). Qed.
Lemma lem1379344 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1379343 x y h1 h2 h3 h4) (@lem1378637 x y h3)). Qed.
Lemma lem1379345 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1379342 x y h1 h2 h3 h4) (fun h5 : False => @lem1378399 x y h4)). Qed.
Lemma lem1379346 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1379345 x y h1 h2 h3 h4) (@lem1378399 x y h4)). Qed.
Lemma lem1379347 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : (term26 x y) = False.
Proof. exact (prop_ext (fun h5 : term26 x y => @lem1379344 x y h1 h2 h3 h4) (fun h5 : False => @lem1378295 x y h3)). Qed.
Lemma lem1379348 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1379347 x y h1 h2 h3 h4) (@lem1378295 x y h3)). Qed.
Lemma lem1379349 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1379346 x y h1 h2 h3 h4) (fun h5 : False => @lem1378399 x y h4)). Qed.
Lemma lem1379350 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term53 x y) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1379349 x y h1 h2 h3 h4) (@lem1378399 x y h4)). Qed.
Lemma lem1379351 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : (term26 x y) = False.
Proof. exact (prop_ext (fun h5 : term26 x y => @lem1379348 x y h1 h2 h3 h4) (fun h5 : False => @lem1378295 x y h3)). Qed.
Lemma lem1379352 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1379351 x y h1 h2 h3 h4) (@lem1378295 x y h3)). Qed.
Lemma lem1379353 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1379352 x y h1 h2 h3 h4) (fun h5 : False => @lem1378207 h2)). Qed.
Lemma lem1379354 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term26 x y) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1379353 x y h1 h2 h3 h4) (@lem1378207 h2)). Qed.
Lemma lem1379355 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term53 x y) : False.
Proof. exact (or_elim (@lem1378184 x y h4) (fun h0 : term26 x y => @lem1379354 x y h2 h3 h0 h4) (fun h0 : x = y => @lem1379350 x y h1 h2 h4 h0)). Qed.
Lemma lem1379356 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term57 x y) : False.
Proof. exact (or_elim (@lem1378177 x y h4) (fun h0 : term53 x y => @lem1379355 x y h1 h2 h3 h0) (fun h0 : term50 x y => @lem1379339 x y h1 h2 h0)). Qed.
Lemma lem1379357 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term57 x y) : (term57 x y) = False.
Proof. exact (prop_ext (fun h5 : term57 x y => @lem1379356 x y h1 h2 h3 h4) (fun h5 : False => @lem1378177 x y h4)). Qed.
Lemma lem1379358 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term57 x y) : False.
Proof. exact (EQ_MP (@lem1379357 x y h1 h2 h3 h4) (@lem1378177 x y h4)). Qed.
Lemma lem1379359 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term57 x y) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1379358 x y h1 h2 h3 h4) (fun h5 : False => @lem1378079 h3)). Qed.
Lemma lem1379360 (x : real) (y : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term57 x y) : False.
Proof. exact (EQ_MP (@lem1379359 x y h1 h2 h3 h4) (@lem1378079 h3)). Qed.
Lemma lem1379361 (x : real) (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term67 x) : False.
Proof. exact (ex_elim (@lem1377994 x h4) (fun y : real => fun h0 : term66 x y => @lem1379360 x y h1 h2 h3 h0)). Qed.
Lemma lem1379362 (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1377339 h4) (fun x : real => fun h0 : term72 x => @lem1379361 x h1 h2 h3 h0)). Qed.
Lemma lem1379363 (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term10) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1379362 h1 h2 h3 h4) (fun h5 : False => @lem1377704 h3)). Qed.
Lemma lem1379364 (h1 : term39) (h2 : term17) (h3 : term34) (h4 : term10) : False.
Proof. exact (EQ_MP (@lem1379363 h1 h2 h3 h4) (@lem1377704 h3)). Qed.
Lemma lem1379365 (h1 : term39) (h2 : term34) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1379364 h1 h0 h2 h3). Qed.
Lemma lem1379366 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1379367 (h1 : term39) (h2 : term34) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1379366) (@lem1379365 h1 h2 h3)). Qed.
Lemma lem1379368 (h1 : term39) (h2 : term10) : term20.
Proof. exact (fun h0 : term34 => @lem1379367 h1 h0 h2). Qed.
Lemma lem1379369 (h1 : term10) : term23.
Proof. exact (fun h0 : term39 => @lem1379368 h0 h1). Qed.
Lemma lem1379370 : term25.
Proof. exact (fun h0 : term10 => @lem1379369 h0). Qed.
Lemma lem1379371 : term11.
Proof. exact (EQ_MP (@lem1376965) (@lem1379370)). Qed.
Lemma lem1379373 : term11.
Proof. exact (@lem1376725 (@lem1379371)). Qed.
Lemma lem1379374 (h1 : term10) : term22.
Proof. exact (@lem1379373 (@lem1376710 h1)). Qed.
Lemma lem1379375 (h1 : term10) : term19.
Proof. exact (@lem1379374 h1 (@lem1339379)). Qed.
Lemma lem1379376 (h1 : term10) : term15.
Proof. exact (@lem1379375 h1 (@lem1339697)). Qed.
Lemma lem1379377 (h1 : term10) : False.
Proof. exact (@lem1379376 h1 (@lem1341566)). Qed.
Lemma lem1379378 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1379377 h1) (fun h2 : False => @lem1376710 h1)). Qed.
Lemma lem1379379 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1379378 h1) (@lem1376710 h1)). Qed.
Lemma lem1379380 : term9.
Proof. exact (fun h0 : term10 => @lem1379379 h0). Qed.
Lemma lem1379381 : term8.
Proof. exact (EQ_MP (@lem1376709) (@lem1379380)). Qed.
