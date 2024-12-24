Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_MONO_LT_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_NOT_LT_spec.
Require Import SQRT_MONO_LE_spec.
Require Import SQRT_MONO_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1951687 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1951688 : term1 = term2.
Proof. exact (@lem1951687 term1). Qed.
Lemma lem1951689 : term2 = term1.
Proof. exact (SYM (@lem1951688)). Qed.
Lemma lem1951690 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1951693 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1951694 : term5.
Proof. exact (fun h0 : term4 => @lem1951693 h0). Qed.
Lemma lem1951695 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1951696 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1951697 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1951695 h2 (@lem1951696 h1)). Qed.
Lemma lem1951698 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1951697 h1 h0). Qed.
Lemma lem1951699 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1951700 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1951698 h1 (@lem1951699 h2)). Qed.
Lemma lem1951701 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1951700 h0 h1). Qed.
Lemma lem1951702 : term7.
Proof. exact (fun h0 : term5 => @lem1951701 h0). Qed.
Lemma lem1951705 : term5.
Proof. exact (@lem1951702 (@lem1951694)). Qed.
Lemma lem1951741 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1951742 : term8 = term9.
Proof. exact (@lem1951741 term10). Qed.
Lemma lem1951751 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1951752 : term12 = term13.
Proof. exact (MK_COMB (@lem1951751) (@lem1951742)). Qed.
Lemma lem1951755 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1951756 : term15 = term16.
Proof. exact (MK_COMB (@lem1951755) (@lem1951752)). Qed.
Lemma lem1951759 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1951766 : term4 = term18.
Proof. exact (MK_COMB (@lem1951759) (@lem1951756)). Qed.
Lemma lem1951773 (y : real) (x : real) : ((term19 x y) = (real_le y x)) = ((term19 x y) = (real_le y x)).
Proof. exact (eq_refl ((term19 x y) = (real_le y x))). Qed.
Lemma lem1951774 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1951773 y x)). Qed.
Lemma lem1951775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951776 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1951775) (@lem1951774 x)). Qed.
Lemma lem1951777 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1951776 x)). Qed.
Lemma lem1951778 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951779 : term10 = term10.
Proof. exact (MK_COMB (@lem1951778) (@lem1951777)). Qed.
Lemma lem1951780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1951781 : term9 = term9.
Proof. exact (MK_COMB (@lem1951780) (@lem1951779)). Qed.
Lemma lem1951786 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1951787 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : real => @lem1951786 x y)). Qed.
Lemma lem1951788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951789 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1951788) (@lem1951787 x)). Qed.
Lemma lem1951790 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1951789 x)). Qed.
Lemma lem1951791 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951792 : term27 = term27.
Proof. exact (MK_COMB (@lem1951791) (@lem1951790)). Qed.
Lemma lem1951793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1951794 : term11 = term11.
Proof. exact (MK_COMB (@lem1951793) (@lem1951792)). Qed.
Lemma lem1951795 : term13 = term13.
Proof. exact (MK_COMB (@lem1951794) (@lem1951781)). Qed.
Lemma lem1951800 (x : real) (y : real) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1951801 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1951800 x y)). Qed.
Lemma lem1951802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951803 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1951802) (@lem1951801 x)). Qed.
Lemma lem1951804 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1951803 x)). Qed.
Lemma lem1951805 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951806 : term32 = term32.
Proof. exact (MK_COMB (@lem1951805) (@lem1951804)). Qed.
Lemma lem1951807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1951808 : term14 = term14.
Proof. exact (MK_COMB (@lem1951807) (@lem1951806)). Qed.
Lemma lem1951809 : term16 = term16.
Proof. exact (MK_COMB (@lem1951808) (@lem1951795)). Qed.
Lemma lem1951814 (x : real) (y : real) : ((term33 x y) = (real_lt x y)) = ((term33 x y) = (real_lt x y)).
Proof. exact (eq_refl ((term33 x y) = (real_lt x y))). Qed.
Lemma lem1951815 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1951814 x y)). Qed.
Lemma lem1951816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951817 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1951816) (@lem1951815 x)). Qed.
Lemma lem1951818 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1951817 x)). Qed.
Lemma lem1951819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951820 : term1 = term1.
Proof. exact (MK_COMB (@lem1951819) (@lem1951818)). Qed.
Lemma lem1951821 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1951822 : term3 = term3.
Proof. exact (MK_COMB (@lem1951821) (@lem1951820)). Qed.
Lemma lem1951823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1951824 : term17 = term17.
Proof. exact (MK_COMB (@lem1951823) (@lem1951822)). Qed.
Lemma lem1951825 : term18 = term18.
Proof. exact (MK_COMB (@lem1951824) (@lem1951809)). Qed.
Lemma lem1951886 : term4 = term18.
Proof. exact (TRANS (@lem1951766) (@lem1951825)). Qed.
Lemma lem1951887 : term18 = term4.
Proof. exact (SYM (@lem1951886)). Qed.
Lemma lem1951888 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1951889 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1951890 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1951891 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1951906 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (@lem17646 (term33 x y) (real_lt x y)). Qed.
Lemma lem1951907 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1951908 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1951907 (term34 x)). Qed.
Lemma lem1951909 (x : real) (y : real) : (term43 x y) = ((term33 x y) = (real_lt x y)).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1951910 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1951911 (x : real) (y : real) : (term44 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1951910) (@lem1951909 x y)). Qed.
Lemma lem1951912 (x : real) (y : real) : (term44 x y) = (term38 x y).
Proof. exact (TRANS (@lem1951911 x y) (@lem1951906 x y)). Qed.
Lemma lem1951913 (x : real) : (term45 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1951912 x y)). Qed.
Lemma lem1951914 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1951915 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1951914) (@lem1951913 x)). Qed.
Lemma lem1951916 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1951908 x) (@lem1951915 x)). Qed.
Lemma lem1951917 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1951918 : term3 = term48.
Proof. exact (@lem1951917 term36). Qed.
Lemma lem1951919 (x : real) : (term49 x) = (term35 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1951920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1951921 (x : real) : (term50 x) = (term41 x).
Proof. exact (MK_COMB (@lem1951920) (@lem1951919 x)). Qed.
Lemma lem1951922 (x : real) : (term50 x) = (term47 x).
Proof. exact (TRANS (@lem1951921 x) (@lem1951916 x)). Qed.
Lemma lem1951923 : term51 = term52.
Proof. exact (fun_ext (fun x : real => @lem1951922 x)). Qed.
Lemma lem1951924 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1951925 : term48 = term53.
Proof. exact (MK_COMB (@lem1951924) (@lem1951923)). Qed.
Lemma lem1951926 : term3 = term53.
Proof. exact (TRANS (@lem1951918) (@lem1951925)). Qed.
Lemma lem1951932 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1951933 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1951932 real P Q). Qed.
Lemma lem1951934 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1951933 (term60 x) (term61 x)). Qed.
Lemma lem1951935 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1951936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1951937 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1951936) (@lem1951935 x y)). Qed.
Lemma lem1951938 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1951939 (x : real) (y : real) : (term68 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1951937 x y) (@lem1951938 x y)). Qed.
Lemma lem1951940 (x : real) : (term69 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1951939 x y)). Qed.
Lemma lem1951941 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1951942 (x : real) : (term58 x) = (term47 x).
Proof. exact (MK_COMB (@lem1951941) (@lem1951940 x)). Qed.
Lemma lem1951943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1951944 (x : real) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1951943) (@lem1951942 x)). Qed.
Lemma lem1951945 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1951946 (x : real) : (term72 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1951945 x y)). Qed.
Lemma lem1951947 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1951948 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1951947) (@lem1951946 x)). Qed.
Lemma lem1951949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1951950 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1951949) (@lem1951948 x)). Qed.
Lemma lem1951951 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1951952 (x : real) : (term77 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1951951 x y)). Qed.
Lemma lem1951953 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1951954 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1951953) (@lem1951952 x)). Qed.
Lemma lem1951955 (x : real) : (term59 x) = (term80 x).
Proof. exact (MK_COMB (@lem1951950 x) (@lem1951954 x)). Qed.
Lemma lem1951956 (x : real) : ((term58 x) = (term59 x)) = ((term47 x) = (term80 x)).
Proof. exact (MK_COMB (@lem1951944 x) (@lem1951955 x)). Qed.
Lemma lem1951957 (x : real) : (term47 x) = (term80 x).
Proof. exact (EQ_MP (@lem1951956 x) (@lem1951934 x)). Qed.
Lemma lem1952054 : term52 = term81.
Proof. exact (fun_ext (fun x : real => @lem1951957 x)). Qed.
Lemma lem1952055 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952056 : term53 = term82.
Proof. exact (MK_COMB (@lem1952055) (@lem1952054)). Qed.
Lemma lem1952058 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1952059 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1952058 real P Q). Qed.
Lemma lem1952060 : term83 = term84.
Proof. exact (@lem1952059 term85 term86). Qed.
Lemma lem1952061 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1952062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952063 (x : real) : (term88 x) = (term76 x).
Proof. exact (MK_COMB (@lem1952062) (@lem1952061 x)). Qed.
Lemma lem1952064 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1952065 (x : real) : (term90 x) = (term80 x).
Proof. exact (MK_COMB (@lem1952063 x) (@lem1952064 x)). Qed.
Lemma lem1952066 : term91 = term81.
Proof. exact (fun_ext (fun x : real => @lem1952065 x)). Qed.
Lemma lem1952067 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952068 : term83 = term82.
Proof. exact (MK_COMB (@lem1952067) (@lem1952066)). Qed.
Lemma lem1952069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1952070 : term92 = term93.
Proof. exact (MK_COMB (@lem1952069) (@lem1952068)). Qed.
Lemma lem1952071 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1952072 : term94 = term85.
Proof. exact (fun_ext (fun x : real => @lem1952071 x)). Qed.
Lemma lem1952073 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952074 : term95 = term96.
Proof. exact (MK_COMB (@lem1952073) (@lem1952072)). Qed.
Lemma lem1952075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952076 : term97 = term98.
Proof. exact (MK_COMB (@lem1952075) (@lem1952074)). Qed.
Lemma lem1952077 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1952078 : term99 = term86.
Proof. exact (fun_ext (fun x : real => @lem1952077 x)). Qed.
Lemma lem1952079 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952080 : term100 = term101.
Proof. exact (MK_COMB (@lem1952079) (@lem1952078)). Qed.
Lemma lem1952081 : term84 = term102.
Proof. exact (MK_COMB (@lem1952076) (@lem1952080)). Qed.
Lemma lem1952082 : (term83 = term84) = (term82 = term102).
Proof. exact (MK_COMB (@lem1952070) (@lem1952081)). Qed.
Lemma lem1952083 : term82 = term102.
Proof. exact (EQ_MP (@lem1952082) (@lem1952060)). Qed.
Lemma lem1952188 : term53 = term102.
Proof. exact (TRANS (@lem1952056) (@lem1952083)). Qed.
Lemma lem1952190 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1952191 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1952190 real P Q). Qed.
Lemma lem1952192 : term84 = term83.
Proof. exact (@lem1952191 term85 term86). Qed.
Lemma lem1952193 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1952194 : term94 = term85.
Proof. exact (fun_ext (fun x : real => @lem1952193 x)). Qed.
Lemma lem1952195 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952196 : term95 = term96.
Proof. exact (MK_COMB (@lem1952195) (@lem1952194)). Qed.
Lemma lem1952197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952198 : term97 = term98.
Proof. exact (MK_COMB (@lem1952197) (@lem1952196)). Qed.
Lemma lem1952199 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1952200 : term99 = term86.
Proof. exact (fun_ext (fun x : real => @lem1952199 x)). Qed.
Lemma lem1952201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952202 : term100 = term101.
Proof. exact (MK_COMB (@lem1952201) (@lem1952200)). Qed.
Lemma lem1952203 : term84 = term102.
Proof. exact (MK_COMB (@lem1952198) (@lem1952202)). Qed.
Lemma lem1952204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1952205 : term103 = term104.
Proof. exact (MK_COMB (@lem1952204) (@lem1952203)). Qed.
Lemma lem1952206 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1952207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952208 (x : real) : (term88 x) = (term76 x).
Proof. exact (MK_COMB (@lem1952207) (@lem1952206 x)). Qed.
Lemma lem1952209 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1952210 (x : real) : (term90 x) = (term80 x).
Proof. exact (MK_COMB (@lem1952208 x) (@lem1952209 x)). Qed.
Lemma lem1952211 : term91 = term81.
Proof. exact (fun_ext (fun x : real => @lem1952210 x)). Qed.
Lemma lem1952212 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952213 : term83 = term82.
Proof. exact (MK_COMB (@lem1952212) (@lem1952211)). Qed.
Lemma lem1952214 : (term84 = term83) = (term102 = term82).
Proof. exact (MK_COMB (@lem1952205) (@lem1952213)). Qed.
Lemma lem1952215 : term102 = term82.
Proof. exact (EQ_MP (@lem1952214) (@lem1952192)). Qed.
Lemma lem1952217 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1952218 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1952217 real P Q). Qed.
Lemma lem1952219 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1952218 (term60 x) (term61 x)). Qed.
Lemma lem1952220 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1952221 (x : real) : (term72 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1952220 x y)). Qed.
Lemma lem1952222 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952223 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1952222) (@lem1952221 x)). Qed.
Lemma lem1952224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952225 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1952224) (@lem1952223 x)). Qed.
Lemma lem1952226 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1952227 (x : real) : (term77 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1952226 x y)). Qed.
Lemma lem1952228 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952229 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1952228) (@lem1952227 x)). Qed.
Lemma lem1952230 (x : real) : (term59 x) = (term80 x).
Proof. exact (MK_COMB (@lem1952225 x) (@lem1952229 x)). Qed.
Lemma lem1952231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1952232 (x : real) : (term105 x) = (term106 x).
Proof. exact (MK_COMB (@lem1952231) (@lem1952230 x)). Qed.
Lemma lem1952233 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1952234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952235 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1952234) (@lem1952233 x y)). Qed.
Lemma lem1952236 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1952237 (x : real) (y : real) : (term68 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1952235 x y) (@lem1952236 x y)). Qed.
Lemma lem1952238 (x : real) : (term69 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1952237 x y)). Qed.
Lemma lem1952239 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952240 (x : real) : (term58 x) = (term47 x).
Proof. exact (MK_COMB (@lem1952239) (@lem1952238 x)). Qed.
Lemma lem1952241 (x : real) : ((term59 x) = (term58 x)) = ((term80 x) = (term47 x)).
Proof. exact (MK_COMB (@lem1952232 x) (@lem1952240 x)). Qed.
Lemma lem1952242 (x : real) : (term80 x) = (term47 x).
Proof. exact (EQ_MP (@lem1952241 x) (@lem1952219 x)). Qed.
Lemma lem1952243 : term81 = term52.
Proof. exact (fun_ext (fun x : real => @lem1952242 x)). Qed.
Lemma lem1952244 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1952245 : term82 = term53.
Proof. exact (MK_COMB (@lem1952244) (@lem1952243)). Qed.
Lemma lem1952246 : term102 = term53.
Proof. exact (TRANS (@lem1952215) (@lem1952245)). Qed.
Lemma lem1952247 : term53 = term53.
Proof. exact (TRANS (@lem1952188) (@lem1952246)). Qed.
Lemma lem1952248 : term3 = term53.
Proof. exact (TRANS (@lem1951926) (@lem1952247)). Qed.
Lemma lem1952249 (h1 : term3) : term53.
Proof. exact (EQ_MP (@lem1952248) (@lem1951888 h1)). Qed.
Lemma lem1952256 (x : real) (y : real) : (term28 x y) = (term107 x y).
Proof. exact (@lem17265 (real_le x y) (term108 x y)). Qed.
Lemma lem1952257 (x : real) : (term29 x) = (term109 x).
Proof. exact (fun_ext (fun y : real => @lem1952256 x y)). Qed.
Lemma lem1952258 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952259 (x : real) : (term30 x) = (term110 x).
Proof. exact (MK_COMB (@lem1952258) (@lem1952257 x)). Qed.
Lemma lem1952260 : term31 = term111.
Proof. exact (fun_ext (fun x : real => @lem1952259 x)). Qed.
Lemma lem1952261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952318 : term32 = term112.
Proof. exact (MK_COMB (@lem1952261) (@lem1952260)). Qed.
Lemma lem1952319 (h1 : term32) : term112.
Proof. exact (EQ_MP (@lem1952318) (@lem1951889 h1)). Qed.
Lemma lem1952326 (x : real) (y : real) : (term23 x y) = (term113 x y).
Proof. exact (@lem17265 (real_lt x y) (term33 x y)). Qed.
Lemma lem1952327 (x : real) : (term24 x) = (term114 x).
Proof. exact (fun_ext (fun y : real => @lem1952326 x y)). Qed.
Lemma lem1952328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952329 (x : real) : (term25 x) = (term115 x).
Proof. exact (MK_COMB (@lem1952328) (@lem1952327 x)). Qed.
Lemma lem1952330 : term26 = term116.
Proof. exact (fun_ext (fun x : real => @lem1952329 x)). Qed.
Lemma lem1952331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952388 : term27 = term117.
Proof. exact (MK_COMB (@lem1952331) (@lem1952330)). Qed.
Lemma lem1952389 (h1 : term27) : term117.
Proof. exact (EQ_MP (@lem1952388) (@lem1951890 h1)). Qed.
Lemma lem1952393 (x : real) (y : real) : (term118 x y) = (real_lt x y).
Proof. exact (@lem16933 (real_lt x y)). Qed.
Lemma lem1952395 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1952396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1952397 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1952396) (@lem1952393 x y)). Qed.
Lemma lem1952398 (y : real) (x : real) : (term121 y x) = (term122 y x).
Proof. exact (MK_COMB (@lem1952397 x y) (@lem1952395 y x)). Qed.
Lemma lem1952403 (y : real) (x : real) : (term123 y x) = (term123 y x).
Proof. exact (eq_refl (term123 y x)). Qed.
Lemma lem1952404 (y : real) (x : real) : (term124 y x) = (term125 y x).
Proof. exact (MK_COMB (@lem1952403 y x) (@lem1952398 y x)). Qed.
Lemma lem1952405 (y : real) (x : real) : ((term19 x y) = (real_le y x)) = (term124 y x).
Proof. exact (@lem17784 (term19 x y) (real_le y x)). Qed.
Lemma lem1952406 (y : real) (x : real) : ((term19 x y) = (real_le y x)) = (term125 y x).
Proof. exact (TRANS (@lem1952405 y x) (@lem1952404 y x)). Qed.
Lemma lem1952407 (x : real) : (term20 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1952406 y x)). Qed.
Lemma lem1952408 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952409 (x : real) : (term21 x) = (term127 x).
Proof. exact (MK_COMB (@lem1952408) (@lem1952407 x)). Qed.
Lemma lem1952410 : term22 = term128.
Proof. exact (fun_ext (fun x : real => @lem1952409 x)). Qed.
Lemma lem1952411 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952412 : term10 = term129.
Proof. exact (MK_COMB (@lem1952411) (@lem1952410)). Qed.
Lemma lem1952418 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1952419 (P : real -> Prop) (Q : real -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem1952418 real P Q). Qed.
Lemma lem1952420 (x : real) : (term134 x) = (term135 x).
Proof. exact (@lem1952419 (term136 x) (term137 x)). Qed.
Lemma lem1952421 (y : real) (x : real) : (term138 x y) = (term139 y x).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1952422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1952423 (y : real) (x : real) : (term140 x y) = (term123 y x).
Proof. exact (MK_COMB (@lem1952422) (@lem1952421 y x)). Qed.
Lemma lem1952424 (y : real) (x : real) : (term141 x y) = (term122 y x).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1952425 (y : real) (x : real) : (term142 x y) = (term125 y x).
Proof. exact (MK_COMB (@lem1952423 y x) (@lem1952424 y x)). Qed.
Lemma lem1952426 (x : real) : (term143 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1952425 y x)). Qed.
Lemma lem1952427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952428 (x : real) : (term134 x) = (term127 x).
Proof. exact (MK_COMB (@lem1952427) (@lem1952426 x)). Qed.
Lemma lem1952429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1952430 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1952429) (@lem1952428 x)). Qed.
Lemma lem1952431 (y : real) (x : real) : (term138 x y) = (term139 y x).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1952432 (x : real) : (term146 x) = (term136 x).
Proof. exact (fun_ext (fun y : real => @lem1952431 y x)). Qed.
Lemma lem1952433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952434 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1952433) (@lem1952432 x)). Qed.
Lemma lem1952435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1952436 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1952435) (@lem1952434 x)). Qed.
Lemma lem1952437 (y : real) (x : real) : (term141 x y) = (term122 y x).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1952438 (x : real) : (term151 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1952437 y x)). Qed.
Lemma lem1952439 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952440 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1952439) (@lem1952438 x)). Qed.
Lemma lem1952441 (x : real) : (term135 x) = (term154 x).
Proof. exact (MK_COMB (@lem1952436 x) (@lem1952440 x)). Qed.
Lemma lem1952442 (x : real) : ((term134 x) = (term135 x)) = ((term127 x) = (term154 x)).
Proof. exact (MK_COMB (@lem1952430 x) (@lem1952441 x)). Qed.
Lemma lem1952443 (x : real) : (term127 x) = (term154 x).
Proof. exact (EQ_MP (@lem1952442 x) (@lem1952420 x)). Qed.
Lemma lem1952540 : term128 = term155.
Proof. exact (fun_ext (fun x : real => @lem1952443 x)). Qed.
Lemma lem1952541 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952542 : term129 = term156.
Proof. exact (MK_COMB (@lem1952541) (@lem1952540)). Qed.
Lemma lem1952544 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1952545 (P : real -> Prop) (Q : real -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem1952544 real P Q). Qed.
Lemma lem1952546 : term157 = term158.
Proof. exact (@lem1952545 term159 term160). Qed.
Lemma lem1952547 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1952548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1952549 (x : real) : (term162 x) = (term150 x).
Proof. exact (MK_COMB (@lem1952548) (@lem1952547 x)). Qed.
Lemma lem1952550 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1952551 (x : real) : (term164 x) = (term154 x).
Proof. exact (MK_COMB (@lem1952549 x) (@lem1952550 x)). Qed.
Lemma lem1952552 : term165 = term155.
Proof. exact (fun_ext (fun x : real => @lem1952551 x)). Qed.
Lemma lem1952553 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952554 : term157 = term156.
Proof. exact (MK_COMB (@lem1952553) (@lem1952552)). Qed.
Lemma lem1952555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1952556 : term166 = term167.
Proof. exact (MK_COMB (@lem1952555) (@lem1952554)). Qed.
Lemma lem1952557 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1952558 : term168 = term159.
Proof. exact (fun_ext (fun x : real => @lem1952557 x)). Qed.
Lemma lem1952559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952560 : term169 = term170.
Proof. exact (MK_COMB (@lem1952559) (@lem1952558)). Qed.
Lemma lem1952561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1952562 : term171 = term172.
Proof. exact (MK_COMB (@lem1952561) (@lem1952560)). Qed.
Lemma lem1952563 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1952564 : term173 = term160.
Proof. exact (fun_ext (fun x : real => @lem1952563 x)). Qed.
Lemma lem1952565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952566 : term174 = term175.
Proof. exact (MK_COMB (@lem1952565) (@lem1952564)). Qed.
Lemma lem1952567 : term158 = term176.
Proof. exact (MK_COMB (@lem1952562) (@lem1952566)). Qed.
Lemma lem1952568 : (term157 = term158) = (term156 = term176).
Proof. exact (MK_COMB (@lem1952556) (@lem1952567)). Qed.
Lemma lem1952569 : term156 = term176.
Proof. exact (EQ_MP (@lem1952568) (@lem1952546)). Qed.
Lemma lem1952676 : term129 = term176.
Proof. exact (TRANS (@lem1952542) (@lem1952569)). Qed.
Lemma lem1952677 : term10 = term176.
Proof. exact (TRANS (@lem1952412) (@lem1952676)). Qed.
Lemma lem1952678 (h1 : term10) : term176.
Proof. exact (EQ_MP (@lem1952677) (@lem1951891 h1)). Qed.
Lemma lem1952679 (x : real) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1952699 (x : real) (y : real) : (term107 x y) = (term107 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1952700 (x : real) : (term109 x) = (term109 x).
Proof. exact (fun_ext (fun y : real => @lem1952699 x y)). Qed.
Lemma lem1952701 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952702 (x : real) : (term110 x) = (term110 x).
Proof. exact (MK_COMB (@lem1952701) (@lem1952700 x)). Qed.
Lemma lem1952703 : term111 = term111.
Proof. exact (fun_ext (fun x : real => @lem1952702 x)). Qed.
Lemma lem1952704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952705 : term112 = term112.
Proof. exact (MK_COMB (@lem1952704) (@lem1952703)). Qed.
Lemma lem1952706 (h1 : term32) : term112.
Proof. exact (EQ_MP (@lem1952705) (@lem1952319 h1)). Qed.
Lemma lem1952725 (x : real) (y : real) : (term113 x y) = (term113 x y).
Proof. exact (eq_refl (term113 x y)). Qed.
Lemma lem1952726 (x : real) : (term114 x) = (term114 x).
Proof. exact (fun_ext (fun y : real => @lem1952725 x y)). Qed.
Lemma lem1952727 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952728 (x : real) : (term115 x) = (term115 x).
Proof. exact (MK_COMB (@lem1952727) (@lem1952726 x)). Qed.
Lemma lem1952729 : term116 = term116.
Proof. exact (fun_ext (fun x : real => @lem1952728 x)). Qed.
Lemma lem1952730 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952731 : term117 = term117.
Proof. exact (MK_COMB (@lem1952730) (@lem1952729)). Qed.
Lemma lem1952732 (h1 : term27) : term117.
Proof. exact (EQ_MP (@lem1952731) (@lem1952389 h1)). Qed.
Lemma lem1952745 (y : real) (x : real) : (term122 y x) = (term122 y x).
Proof. exact (eq_refl (term122 y x)). Qed.
Lemma lem1952746 (x : real) : (term137 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1952745 y x)). Qed.
Lemma lem1952747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952748 (x : real) : (term153 x) = (term153 x).
Proof. exact (MK_COMB (@lem1952747) (@lem1952746 x)). Qed.
Lemma lem1952749 : term160 = term160.
Proof. exact (fun_ext (fun x : real => @lem1952748 x)). Qed.
Lemma lem1952750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952751 : term175 = term175.
Proof. exact (MK_COMB (@lem1952750) (@lem1952749)). Qed.
Lemma lem1952768 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1952769 (x : real) : (term136 x) = (term136 x).
Proof. exact (fun_ext (fun y : real => @lem1952768 y x)). Qed.
Lemma lem1952770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952771 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1952770) (@lem1952769 x)). Qed.
Lemma lem1952772 : term159 = term159.
Proof. exact (fun_ext (fun x : real => @lem1952771 x)). Qed.
Lemma lem1952773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952774 : term170 = term170.
Proof. exact (MK_COMB (@lem1952773) (@lem1952772)). Qed.
Lemma lem1952775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1952776 : term172 = term172.
Proof. exact (MK_COMB (@lem1952775) (@lem1952774)). Qed.
Lemma lem1952777 : term176 = term176.
Proof. exact (MK_COMB (@lem1952776) (@lem1952751)). Qed.
Lemma lem1952778 (h1 : term10) : term176.
Proof. exact (EQ_MP (@lem1952777) (@lem1952678 h1)). Qed.
Lemma lem1952820 (x : real) (y : real) (h1 : term38 x y) : term38 x y.
Proof. exact (h1). Qed.
Lemma lem1952821 (h1 : term10) : term175.
Proof. exact (proj2 (@lem1952778 h1)). Qed.
Lemma lem1952822 (h1 : term10) : term170.
Proof. exact (proj1 (@lem1952778 h1)). Qed.
Lemma lem1952823 (x : real) (y : real) (h1 : term63 x y) : term63 x y.
Proof. exact (h1). Qed.
Lemma lem1952824 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (h1). Qed.
Lemma lem1952836 (x : real) (y : real) : (term107 x y) = (term107 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1952837 (x : real) : (term109 x) = (term109 x).
Proof. exact (fun_ext (fun y : real => @lem1952836 x y)). Qed.
Lemma lem1952838 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952839 (x : real) : (term110 x) = (term110 x).
Proof. exact (MK_COMB (@lem1952838) (@lem1952837 x)). Qed.
Lemma lem1952840 : term111 = term111.
Proof. exact (fun_ext (fun x : real => @lem1952839 x)). Qed.
Lemma lem1952841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952843 : term112 = term112.
Proof. exact (MK_COMB (@lem1952841) (@lem1952840)). Qed.
Lemma lem1952844 (h1 : term32) : term112.
Proof. exact (EQ_MP (@lem1952843) (@lem1952706 h1)). Qed.
Lemma lem1952868 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1952869 (x : real) : (term136 x) = (term136 x).
Proof. exact (fun_ext (fun y : real => @lem1952868 y x)). Qed.
Lemma lem1952870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952871 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1952870) (@lem1952869 x)). Qed.
Lemma lem1952872 : term159 = term159.
Proof. exact (fun_ext (fun x : real => @lem1952871 x)). Qed.
Lemma lem1952873 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952875 : term170 = term170.
Proof. exact (MK_COMB (@lem1952873) (@lem1952872)). Qed.
Lemma lem1952876 (h1 : term10) : term170.
Proof. exact (EQ_MP (@lem1952875) (@lem1952822 h1)). Qed.
Lemma lem1952884 (y : real) (x : real) : (term122 y x) = (term122 y x).
Proof. exact (eq_refl (term122 y x)). Qed.
Lemma lem1952885 (x : real) : (term137 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1952884 y x)). Qed.
Lemma lem1952886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952887 (x : real) : (term153 x) = (term153 x).
Proof. exact (MK_COMB (@lem1952886) (@lem1952885 x)). Qed.
Lemma lem1952888 : term160 = term160.
Proof. exact (fun_ext (fun x : real => @lem1952887 x)). Qed.
Lemma lem1952889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952891 : term175 = term175.
Proof. exact (MK_COMB (@lem1952889) (@lem1952888)). Qed.
Lemma lem1952892 (h1 : term10) : term175.
Proof. exact (EQ_MP (@lem1952891) (@lem1952821 h1)). Qed.
Lemma lem1952924 (x : real) (y : real) : (term113 x y) = (term113 x y).
Proof. exact (eq_refl (term113 x y)). Qed.
Lemma lem1952925 (x : real) : (term114 x) = (term114 x).
Proof. exact (fun_ext (fun y : real => @lem1952924 x y)). Qed.
Lemma lem1952926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952927 (x : real) : (term115 x) = (term115 x).
Proof. exact (MK_COMB (@lem1952926) (@lem1952925 x)). Qed.
Lemma lem1952928 : term116 = term116.
Proof. exact (fun_ext (fun x : real => @lem1952927 x)). Qed.
Lemma lem1952929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1952931 : term117 = term117.
Proof. exact (MK_COMB (@lem1952929) (@lem1952928)). Qed.
Lemma lem1952932 (h1 : term27) : term117.
Proof. exact (EQ_MP (@lem1952931) (@lem1952732 h1)). Qed.
Lemma lem1952973 (_27394 : real) (h1 : term32) : term177 _27394.
Proof. exact (@lem1952844 h1 _27394). Qed.
Lemma lem1952974 (_27394 : real) : (term177 _27394) = (term110 _27394).
Proof. exact (eq_refl (term177 _27394)). Qed.
Lemma lem1952975 (_27394 : real) (h1 : term32) : term110 _27394.
Proof. exact (EQ_MP (@lem1952974 _27394) (@lem1952973 _27394 h1)). Qed.
Lemma lem1952976 (_27394 : real) (_27395 : real) (h1 : term32) : term178 _27394 _27395.
Proof. exact (@lem1952975 _27394 h1 _27395). Qed.
Lemma lem1952977 (_27394 : real) (_27395 : real) : (term178 _27394 _27395) = (term107 _27394 _27395).
Proof. exact (eq_refl (term178 _27394 _27395)). Qed.
Lemma lem1952985 (_27398 : real) (h1 : term10) : term161 _27398.
Proof. exact (@lem1952876 h1 _27398). Qed.
Lemma lem1952986 (_27398 : real) : (term161 _27398) = (term148 _27398).
Proof. exact (eq_refl (term161 _27398)). Qed.
Lemma lem1952987 (_27398 : real) (h1 : term10) : term148 _27398.
Proof. exact (EQ_MP (@lem1952986 _27398) (@lem1952985 _27398 h1)). Qed.
Lemma lem1952988 (_27398 : real) (_27399 : real) (h1 : term10) : term138 _27398 _27399.
Proof. exact (@lem1952987 _27398 h1 _27399). Qed.
Lemma lem1952989 (_27399 : real) (_27398 : real) : (term138 _27398 _27399) = (term139 _27399 _27398).
Proof. exact (eq_refl (term138 _27398 _27399)). Qed.
Lemma lem1952991 (_27400 : real) (h1 : term10) : term163 _27400.
Proof. exact (@lem1952892 h1 _27400). Qed.
Lemma lem1952992 (_27400 : real) : (term163 _27400) = (term153 _27400).
Proof. exact (eq_refl (term163 _27400)). Qed.
Lemma lem1952993 (_27400 : real) (h1 : term10) : term153 _27400.
Proof. exact (EQ_MP (@lem1952992 _27400) (@lem1952991 _27400 h1)). Qed.
Lemma lem1952994 (_27400 : real) (_27401 : real) (h1 : term10) : term141 _27400 _27401.
Proof. exact (@lem1952993 _27400 h1 _27401). Qed.
Lemma lem1952995 (_27401 : real) (_27400 : real) : (term141 _27400 _27401) = (term122 _27401 _27400).
Proof. exact (eq_refl (term141 _27400 _27401)). Qed.
Lemma lem1953003 (_27404 : real) (h1 : term27) : term179 _27404.
Proof. exact (@lem1952932 h1 _27404). Qed.
Lemma lem1953004 (_27404 : real) : (term179 _27404) = (term115 _27404).
Proof. exact (eq_refl (term179 _27404)). Qed.
Lemma lem1953005 (_27404 : real) (h1 : term27) : term115 _27404.
Proof. exact (EQ_MP (@lem1953004 _27404) (@lem1953003 _27404 h1)). Qed.
Lemma lem1953006 (_27404 : real) (_27405 : real) (h1 : term27) : term180 _27404 _27405.
Proof. exact (@lem1953005 _27404 h1 _27405). Qed.
Lemma lem1953007 (_27404 : real) (_27405 : real) : (term180 _27404 _27405) = (term113 _27404 _27405).
Proof. exact (eq_refl (term180 _27404 _27405)). Qed.
Lemma lem1953026 (_27394 : real) (_27395 : real) (h1 : term32) : term107 _27394 _27395.
Proof. exact (EQ_MP (@lem1952977 _27394 _27395) (@lem1952976 _27394 _27395 h1)). Qed.
Lemma lem1953038 (_27399 : real) (_27398 : real) (h1 : term10) : term139 _27399 _27398.
Proof. exact (EQ_MP (@lem1952989 _27399 _27398) (@lem1952988 _27398 _27399 h1)). Qed.
Lemma lem1953044 (_27401 : real) (_27400 : real) (h1 : term10) : term122 _27401 _27400.
Proof. exact (EQ_MP (@lem1952995 _27401 _27400) (@lem1952994 _27400 _27401 h1)). Qed.
Lemma lem1953048 (x : real) (y : real) (h1 : term63 x y) : term19 x y.
Proof. exact (proj2 (@lem1952823 x y h1)). Qed.
Lemma lem1953060 (_27404 : real) (_27405 : real) (h1 : term27) : term113 _27404 _27405.
Proof. exact (EQ_MP (@lem1953007 _27404 _27405) (@lem1953006 _27404 _27405 h1)). Qed.
Lemma lem1953074 (x : real) (y : real) (h1 : term67 x y) : term181 x y.
Proof. exact (proj1 (@lem1952824 x y h1)). Qed.
Lemma lem1953078 (x : real) (y : real) (h1 : term63 x y) : term33 x y.
Proof. exact (proj1 (@lem1952823 x y h1)). Qed.
Lemma lem1953079 (x : real) (y : real) (h1 : term63 x y) : term182 x y.
Proof. exact (fun h0 : term181 x y => @lem1953078 x y h1). Qed.
Lemma lem1953081 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1953082 (x : real) (y : real) : (term182 x y) = (term33 x y).
Proof. exact (@lem1953081 (term33 x y)). Qed.
Lemma lem1953083 (x : real) (y : real) (h1 : term63 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1953082 x y) (@lem1953079 x y h1)). Qed.
Lemma lem1953089 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1953090 (_27398 : real) (_27399 : real) : (term139 _27399 _27398) = (term184 _27398 _27399).
Proof. exact (@lem1953089 (term185 _27399 _27398) (term19 _27398 _27399)). Qed.
Lemma lem1953096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1953097 (_27398 : real) (_27399 : real) : (term186 _27399 _27398) = (term187 _27398 _27399).
Proof. exact (MK_COMB (@lem1953096) (@lem1953090 _27398 _27399)). Qed.
Lemma lem1953103 (_27398 : real) (_27399 : real) : (term184 _27398 _27399) = (term184 _27398 _27399).
Proof. exact (eq_refl (term184 _27398 _27399)). Qed.
Lemma lem1953104 (_27398 : real) (_27399 : real) : ((term139 _27399 _27398) = (term184 _27398 _27399)) = ((term184 _27398 _27399) = (term184 _27398 _27399)).
Proof. exact (MK_COMB (@lem1953097 _27398 _27399) (@lem1953103 _27398 _27399)). Qed.
Lemma lem1953106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1953107 (x : Prop) : (x = x) = True.
Proof. exact (@lem1953106 Prop x). Qed.
Lemma lem1953108 (_27398 : real) (_27399 : real) : ((term184 _27398 _27399) = (term184 _27398 _27399)) = True.
Proof. exact (@lem1953107 (term184 _27398 _27399)). Qed.
Lemma lem1953109 (_27398 : real) (_27399 : real) : ((term139 _27399 _27398) = (term184 _27398 _27399)) = True.
Proof. exact (TRANS (@lem1953104 _27398 _27399) (@lem1953108 _27398 _27399)). Qed.
Lemma lem1953110 (_27398 : real) (_27399 : real) : True = ((term139 _27399 _27398) = (term184 _27398 _27399)).
Proof. exact (SYM (@lem1953109 _27398 _27399)). Qed.
Lemma lem1953111 (_27398 : real) (_27399 : real) : (term139 _27399 _27398) = (term184 _27398 _27399).
Proof. exact (EQ_MP (@lem1953110 _27398 _27399) (@lem0)). Qed.
Lemma lem1953112 (_27398 : real) (_27399 : real) (h1 : term10) : term184 _27398 _27399.
Proof. exact (EQ_MP (@lem1953111 _27398 _27399) (@lem1953038 _27399 _27398 h1)). Qed.
Lemma lem1953114 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1953115 (_27399 : real) (_27398 : real) : (term184 _27398 _27399) = (term189 _27399 _27398).
Proof. exact (@lem1953114 (term19 _27398 _27399) (term185 _27399 _27398)). Qed.
Lemma lem1953117 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1953118 (_27398 : real) (_27399 : real) : (term118 _27398 _27399) = (real_lt _27398 _27399).
Proof. exact (@lem1953117 (real_lt _27398 _27399)). Qed.
Lemma lem1953119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1953120 (_27398 : real) (_27399 : real) : (term191 _27398 _27399) = (term192 _27398 _27399).
Proof. exact (MK_COMB (@lem1953119) (@lem1953118 _27398 _27399)). Qed.
Lemma lem1953121 (_27399 : real) (_27398 : real) : (term185 _27399 _27398) = (term185 _27399 _27398).
Proof. exact (eq_refl (term185 _27399 _27398)). Qed.
Lemma lem1953122 (_27399 : real) (_27398 : real) : (term189 _27399 _27398) = (term193 _27399 _27398).
Proof. exact (MK_COMB (@lem1953120 _27398 _27399) (@lem1953121 _27399 _27398)). Qed.
Lemma lem1953123 (_27399 : real) (_27398 : real) : (term184 _27398 _27399) = (term193 _27399 _27398).
Proof. exact (TRANS (@lem1953115 _27399 _27398) (@lem1953122 _27399 _27398)). Qed.
Lemma lem1953126 (_27399 : real) (_27398 : real) (h1 : term10) : term193 _27399 _27398.
Proof. exact (EQ_MP (@lem1953123 _27399 _27398) (@lem1953112 _27398 _27399 h1)). Qed.
Lemma lem1953127 (y : real) (x : real) (h1 : term10) : term194 y x.
Proof. exact (@lem1953126 (sqrt y) (sqrt x) h1). Qed.
Lemma lem1953130 (x : real) (y : real) (h1 : term10) (h2 : term63 x y) : term195 y x.
Proof. exact (@lem1953127 y x h1 (@lem1953083 x y h2)). Qed.
Lemma lem1953131 (x : real) (y : real) (h1 : term10) (h2 : term63 x y) : term196 y x.
Proof. exact (fun h0 : term108 y x => @lem1953130 x y h1 h2). Qed.
Lemma lem1953133 (p : Prop) : (term197 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1953134 (y : real) (x : real) : (term196 y x) = (term195 y x).
Proof. exact (@lem1953133 (term108 y x)). Qed.
Lemma lem1953135 (x : real) (y : real) (h1 : term10) (h2 : term63 x y) : term195 y x.
Proof. exact (EQ_MP (@lem1953134 y x) (@lem1953131 x y h1 h2)). Qed.
Lemma lem1953137 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1953140 (_27394 : real) (_27395 : real) : (term107 _27394 _27395) = (term198 _27394 _27395).
Proof. exact (@lem1953137 (term108 _27394 _27395) (term185 _27394 _27395)). Qed.
Lemma lem1953143 (_27394 : real) (_27395 : real) (h1 : term32) : term198 _27394 _27395.
Proof. exact (EQ_MP (@lem1953140 _27394 _27395) (@lem1953026 _27394 _27395 h1)). Qed.
Lemma lem1953144 (y : real) (x : real) (h1 : term32) : term198 y x.
Proof. exact (@lem1953143 y x h1). Qed.
Lemma lem1953147 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : term185 y x.
Proof. exact (@lem1953144 y x h2 (@lem1953135 x y h1 h3)). Qed.
Lemma lem1953148 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : term199 y x.
Proof. exact (fun h0 : real_le y x => @lem1953147 x y h1 h2 h3). Qed.
Lemma lem1953150 (p : Prop) : (term197 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1953151 (y : real) (x : real) : (term199 y x) = (term185 y x).
Proof. exact (@lem1953150 (real_le y x)). Qed.
Lemma lem1953152 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : term185 y x.
Proof. exact (EQ_MP (@lem1953151 y x) (@lem1953148 x y h1 h2 h3)). Qed.
Lemma lem1953154 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1953157 (_27400 : real) (_27401 : real) : (term122 _27401 _27400) = (term200 _27400 _27401).
Proof. exact (@lem1953154 (real_le _27401 _27400) (real_lt _27400 _27401)). Qed.
Lemma lem1953160 (_27400 : real) (_27401 : real) (h1 : term10) : term200 _27400 _27401.
Proof. exact (EQ_MP (@lem1953157 _27400 _27401) (@lem1953044 _27401 _27400 h1)). Qed.
Lemma lem1953161 (x : real) (y : real) (h1 : term10) : term200 x y.
Proof. exact (@lem1953160 x y h1). Qed.
Lemma lem1953164 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : real_lt x y.
Proof. exact (@lem1953161 x y h1 (@lem1953152 x y h1 h2 h3)). Qed.
Lemma lem1953165 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : term201 x y.
Proof. exact (fun h0 : term19 x y => @lem1953164 x y h1 h2 h3). Qed.
Lemma lem1953167 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1953168 (x : real) (y : real) : (term201 x y) = (real_lt x y).
Proof. exact (@lem1953167 (real_lt x y)). Qed.
Lemma lem1953169 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : real_lt x y.
Proof. exact (EQ_MP (@lem1953168 x y) (@lem1953165 x y h1 h2 h3)). Qed.
Lemma lem1953172 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1953174 (x : real) (y : real) : (term19 x y) = (term202 x y).
Proof. exact (@lem1953172 (real_lt x y)). Qed.
Lemma lem1953177 (x : real) (y : real) (h1 : term63 x y) : term202 x y.
Proof. exact (EQ_MP (@lem1953174 x y) (@lem1953048 x y h1)). Qed.
Lemma lem1953180 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : False.
Proof. exact (@lem1953177 x y h3 (@lem1953169 x y h1 h2 h3)). Qed.
Lemma lem1953181 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : term203.
Proof. exact (fun h0 : ~ False => @lem1953180 x y h1 h2 h3). Qed.
Lemma lem1953183 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1953184 : term203 = False.
Proof. exact (@lem1953183 False). Qed.
Lemma lem1953185 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term63 x y) : False.
Proof. exact (EQ_MP (@lem1953184) (@lem1953181 x y h1 h2 h3)). Qed.
Lemma lem1953187 (x : real) (y : real) (h1 : term67 x y) : real_lt x y.
Proof. exact (proj2 (@lem1952824 x y h1)). Qed.
Lemma lem1953188 (x : real) (y : real) (h1 : term67 x y) : term201 x y.
Proof. exact (fun h0 : term19 x y => @lem1953187 x y h1). Qed.
Lemma lem1953190 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1953191 (x : real) (y : real) : (term201 x y) = (real_lt x y).
Proof. exact (@lem1953190 (real_lt x y)). Qed.
Lemma lem1953192 (x : real) (y : real) (h1 : term67 x y) : real_lt x y.
Proof. exact (EQ_MP (@lem1953191 x y) (@lem1953188 x y h1)). Qed.
Lemma lem1953198 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1953199 (_27404 : real) (_27405 : real) : (term113 _27404 _27405) = (term204 _27404 _27405).
Proof. exact (@lem1953198 (term33 _27404 _27405) (term19 _27404 _27405)). Qed.
Lemma lem1953205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1953206 (_27404 : real) (_27405 : real) : (term205 _27404 _27405) = (term206 _27404 _27405).
Proof. exact (MK_COMB (@lem1953205) (@lem1953199 _27404 _27405)). Qed.
Lemma lem1953212 (_27404 : real) (_27405 : real) : (term204 _27404 _27405) = (term204 _27404 _27405).
Proof. exact (eq_refl (term204 _27404 _27405)). Qed.
Lemma lem1953213 (_27404 : real) (_27405 : real) : ((term113 _27404 _27405) = (term204 _27404 _27405)) = ((term204 _27404 _27405) = (term204 _27404 _27405)).
Proof. exact (MK_COMB (@lem1953206 _27404 _27405) (@lem1953212 _27404 _27405)). Qed.
Lemma lem1953215 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1953216 (x : Prop) : (x = x) = True.
Proof. exact (@lem1953215 Prop x). Qed.
Lemma lem1953217 (_27404 : real) (_27405 : real) : ((term204 _27404 _27405) = (term204 _27404 _27405)) = True.
Proof. exact (@lem1953216 (term204 _27404 _27405)). Qed.
Lemma lem1953218 (_27404 : real) (_27405 : real) : ((term113 _27404 _27405) = (term204 _27404 _27405)) = True.
Proof. exact (TRANS (@lem1953213 _27404 _27405) (@lem1953217 _27404 _27405)). Qed.
Lemma lem1953219 (_27404 : real) (_27405 : real) : True = ((term113 _27404 _27405) = (term204 _27404 _27405)).
Proof. exact (SYM (@lem1953218 _27404 _27405)). Qed.
Lemma lem1953220 (_27404 : real) (_27405 : real) : (term113 _27404 _27405) = (term204 _27404 _27405).
Proof. exact (EQ_MP (@lem1953219 _27404 _27405) (@lem0)). Qed.
Lemma lem1953221 (_27404 : real) (_27405 : real) (h1 : term27) : term204 _27404 _27405.
Proof. exact (EQ_MP (@lem1953220 _27404 _27405) (@lem1953060 _27404 _27405 h1)). Qed.
Lemma lem1953223 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1953224 (_27404 : real) (_27405 : real) : (term204 _27404 _27405) = (term207 _27404 _27405).
Proof. exact (@lem1953223 (term19 _27404 _27405) (term33 _27404 _27405)). Qed.
Lemma lem1953226 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1953227 (_27404 : real) (_27405 : real) : (term118 _27404 _27405) = (real_lt _27404 _27405).
Proof. exact (@lem1953226 (real_lt _27404 _27405)). Qed.
Lemma lem1953228 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1953229 (_27404 : real) (_27405 : real) : (term191 _27404 _27405) = (term192 _27404 _27405).
Proof. exact (MK_COMB (@lem1953228) (@lem1953227 _27404 _27405)). Qed.
Lemma lem1953230 (_27404 : real) (_27405 : real) : (term33 _27404 _27405) = (term33 _27404 _27405).
Proof. exact (eq_refl (term33 _27404 _27405)). Qed.
Lemma lem1953231 (_27404 : real) (_27405 : real) : (term207 _27404 _27405) = (term23 _27404 _27405).
Proof. exact (MK_COMB (@lem1953229 _27404 _27405) (@lem1953230 _27404 _27405)). Qed.
Lemma lem1953232 (_27404 : real) (_27405 : real) : (term204 _27404 _27405) = (term23 _27404 _27405).
Proof. exact (TRANS (@lem1953224 _27404 _27405) (@lem1953231 _27404 _27405)). Qed.
Lemma lem1953235 (_27404 : real) (_27405 : real) (h1 : term27) : term23 _27404 _27405.
Proof. exact (EQ_MP (@lem1953232 _27404 _27405) (@lem1953221 _27404 _27405 h1)). Qed.
Lemma lem1953236 (x : real) (y : real) (h1 : term27) : term23 x y.
Proof. exact (@lem1953235 x y h1). Qed.
Lemma lem1953239 (x : real) (y : real) (h1 : term27) (h2 : term67 x y) : term33 x y.
Proof. exact (@lem1953236 x y h1 (@lem1953192 x y h2)). Qed.
Lemma lem1953240 (x : real) (y : real) (h1 : term27) (h2 : term67 x y) : term182 x y.
Proof. exact (fun h0 : term181 x y => @lem1953239 x y h1 h2). Qed.
Lemma lem1953242 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1953243 (x : real) (y : real) : (term182 x y) = (term33 x y).
Proof. exact (@lem1953242 (term33 x y)). Qed.
Lemma lem1953244 (x : real) (y : real) (h1 : term27) (h2 : term67 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1953243 x y) (@lem1953240 x y h1 h2)). Qed.
Lemma lem1953247 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1953249 (x : real) (y : real) : (term181 x y) = (term208 x y).
Proof. exact (@lem1953247 (term33 x y)). Qed.
Lemma lem1953252 (x : real) (y : real) (h1 : term67 x y) : term208 x y.
Proof. exact (EQ_MP (@lem1953249 x y) (@lem1953074 x y h1)). Qed.
Lemma lem1953255 (x : real) (y : real) (h1 : term27) (h2 : term67 x y) : False.
Proof. exact (@lem1953252 x y h2 (@lem1953244 x y h1 h2)). Qed.
Lemma lem1953256 (x : real) (y : real) (h1 : term27) (h2 : term67 x y) : term203.
Proof. exact (fun h0 : ~ False => @lem1953255 x y h1 h2). Qed.
Lemma lem1953258 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1953259 : term203 = False.
Proof. exact (@lem1953258 False). Qed.
Lemma lem1953260 (x : real) (y : real) (h1 : term27) (h2 : term67 x y) : False.
Proof. exact (EQ_MP (@lem1953259) (@lem1953256 x y h1 h2)). Qed.
Lemma lem1953261 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term38 x y) : False.
Proof. exact (or_elim (@lem1952820 x y h4) (fun h0 : term63 x y => @lem1953185 x y h1 h2 h0) (fun h0 : term67 x y => @lem1953260 x y h3 h0)). Qed.
Lemma lem1953262 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term38 x y) : (term38 x y) = False.
Proof. exact (prop_ext (fun h5 : term38 x y => @lem1953261 x y h1 h2 h3 h4) (fun h5 : False => @lem1952820 x y h4)). Qed.
Lemma lem1953263 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term38 x y) : False.
Proof. exact (EQ_MP (@lem1953262 x y h1 h2 h3 h4) (@lem1952820 x y h4)). Qed.
Lemma lem1953264 (x : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term47 x) : False.
Proof. exact (ex_elim (@lem1952679 x h4) (fun y : real => fun h0 : term46 x y => @lem1953263 x y h1 h2 h3 h0)). Qed.
Lemma lem1953265 (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term3) : False.
Proof. exact (ex_elim (@lem1952249 h4) (fun x : real => fun h0 : term52 x => @lem1953264 x h1 h2 h3 h0)). Qed.
Lemma lem1953266 (h1 : term32) (h2 : term27) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1953265 h0 h1 h2 h3). Qed.
Lemma lem1953267 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1953268 (h1 : term32) (h2 : term27) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem1953267) (@lem1953266 h1 h2 h3)). Qed.
Lemma lem1953269 (h1 : term32) (h2 : term3) : term13.
Proof. exact (fun h0 : term27 => @lem1953268 h1 h0 h2). Qed.
Lemma lem1953270 (h1 : term3) : term16.
Proof. exact (fun h0 : term32 => @lem1953269 h0 h1). Qed.
Lemma lem1953271 : term18.
Proof. exact (fun h0 : term3 => @lem1953270 h0). Qed.
Lemma lem1953272 : term4.
Proof. exact (EQ_MP (@lem1951887) (@lem1953271)). Qed.
Lemma lem1953274 : term4.
Proof. exact (@lem1951705 (@lem1953272)). Qed.
Lemma lem1953275 (h1 : term3) : term15.
Proof. exact (@lem1953274 (@lem1951690 h1)). Qed.
Lemma lem1953276 (h1 : term3) : term12.
Proof. exact (@lem1953275 h1 (@lem1951675)). Qed.
Lemma lem1953277 (h1 : term3) : term8.
Proof. exact (@lem1953276 h1 (@lem1950431)). Qed.
Lemma lem1953278 (h1 : term3) : False.
Proof. exact (@lem1953277 h1 (@lem1376537)). Qed.
Lemma lem1953279 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1953278 h1) (fun h2 : False => @lem1951690 h1)). Qed.
Lemma lem1953280 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1953279 h1) (@lem1951690 h1)). Qed.
Lemma lem1953281 : term2.
Proof. exact (fun h0 : term3 => @lem1953280 h0). Qed.
Lemma lem1953282 : term1.
Proof. exact (EQ_MP (@lem1951689) (@lem1953281)). Qed.
