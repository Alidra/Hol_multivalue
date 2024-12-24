Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_SUP_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LTE_TRANS_spec.
Require Import SUP_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5149775 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5149776 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5149777 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5149776 t1) (@lem5149775 t1)). Qed.
Lemma lem5149778 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5149777 t1 t2). Qed.
Lemma lem5149779 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5149780 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5149779 t1 t2) (@lem5149778 t1 t2)). Qed.
Lemma lem5149781 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5149780 t1 t2 t3). Qed.
Lemma lem5149782 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5149783 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5149782 t1 t2 t3) (@lem5149781 t1 t2 t3)). Qed.
Lemma lem5149784 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5149783 t1 t2 t3)). Qed.
Lemma lem5149786 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5149787 : term8 = term9.
Proof. exact (@lem5149786 term8). Qed.
Lemma lem5149788 : term9 = term8.
Proof. exact (SYM (@lem5149787)). Qed.
Lemma lem5149789 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5149792 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5149793 : term12.
Proof. exact (fun h0 : term11 => @lem5149792 h0). Qed.
Lemma lem5149794 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5149795 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5149796 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5149794 h2 (@lem5149795 h1)). Qed.
Lemma lem5149797 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5149796 h1 h0). Qed.
Lemma lem5149798 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5149799 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5149797 h1 (@lem5149798 h2)). Qed.
Lemma lem5149800 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5149799 h0 h1). Qed.
Lemma lem5149801 : term14.
Proof. exact (fun h0 : term12 => @lem5149800 h0). Qed.
Lemma lem5149804 : term12.
Proof. exact (@lem5149801 (@lem5149793)). Qed.
Lemma lem5149888 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5149889 : term15 = term16.
Proof. exact (@lem5149888 term17). Qed.
Lemma lem5149906 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5149907 : term19 = term20.
Proof. exact (MK_COMB (@lem5149906) (@lem5149889)). Qed.
Lemma lem5149910 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5149917 : term11 = term22.
Proof. exact (MK_COMB (@lem5149910) (@lem5149907)). Qed.
Lemma lem5149922 (x : real) (s : real -> Prop) : (term23 x s) = (term23 x s).
Proof. exact (eq_refl (term23 x s)). Qed.
Lemma lem5149923 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5149922 x s)). Qed.
Lemma lem5149924 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5149925 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5149924) (@lem5149923 s)). Qed.
Lemma lem5149928 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5149929 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5149928 s) (@lem5149925 s)). Qed.
Lemma lem5149938 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5149939 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5149938 s) (@lem5149929 s)). Qed.
Lemma lem5149940 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5149939 s)). Qed.
Lemma lem5149941 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5149942 : term17 = term17.
Proof. exact (MK_COMB (@lem5149941) (@lem5149940)). Qed.
Lemma lem5149943 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5149944 : term16 = term16.
Proof. exact (MK_COMB (@lem5149943) (@lem5149942)). Qed.
Lemma lem5149953 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5149954 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5149953 y x z)). Qed.
Lemma lem5149955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5149956 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5149955) (@lem5149954 y x)). Qed.
Lemma lem5149957 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5149956 y x)). Qed.
Lemma lem5149958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5149959 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5149958) (@lem5149957 x)). Qed.
Lemma lem5149960 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5149959 x)). Qed.
Lemma lem5149961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5149962 : term37 = term37.
Proof. exact (MK_COMB (@lem5149961) (@lem5149960)). Qed.
Lemma lem5149963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5149964 : term18 = term18.
Proof. exact (MK_COMB (@lem5149963) (@lem5149962)). Qed.
Lemma lem5149965 : term20 = term20.
Proof. exact (MK_COMB (@lem5149964) (@lem5149944)). Qed.
Lemma lem5149970 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term38 s a x).
Proof. exact (eq_refl (term38 s a x)). Qed.
Lemma lem5149971 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5149970 s a x)). Qed.
Lemma lem5149972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5149973 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5149972) (@lem5149971 s a)). Qed.
Lemma lem5149976 (a : real) (s : real -> Prop) : (term41 a s) = (term41 a s).
Proof. exact (eq_refl (term41 a s)). Qed.
Lemma lem5149977 (s : real -> Prop) (a : real) : ((term42 a s) = (term40 s a)) = ((term42 a s) = (term40 s a)).
Proof. exact (MK_COMB (@lem5149976 a s) (@lem5149973 s a)). Qed.
Lemma lem5149986 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5149987 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5149986 s) (@lem5149977 s a)). Qed.
Lemma lem5149988 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5149987 s a)). Qed.
Lemma lem5149989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5149990 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5149989) (@lem5149988 s)). Qed.
Lemma lem5149991 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5149990 s)). Qed.
Lemma lem5149992 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5149993 : term8 = term8.
Proof. exact (MK_COMB (@lem5149992) (@lem5149991)). Qed.
Lemma lem5149994 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5149995 : term10 = term10.
Proof. exact (MK_COMB (@lem5149994) (@lem5149993)). Qed.
Lemma lem5149996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5149997 : term21 = term21.
Proof. exact (MK_COMB (@lem5149996) (@lem5149995)). Qed.
Lemma lem5149998 : term22 = term22.
Proof. exact (MK_COMB (@lem5149997) (@lem5149965)). Qed.
Lemma lem5150071 : term11 = term22.
Proof. exact (TRANS (@lem5149917) (@lem5149998)). Qed.
Lemma lem5150072 : term22 = term11.
Proof. exact (SYM (@lem5150071)). Qed.
Lemma lem5150073 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5150074 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5150075 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5150091 (s : real -> Prop) (a : real) (x : real) : (term47 s a x) = (term48 s a x).
Proof. exact (@lem17045 (@IN real x s) (real_lt a x)). Qed.
Lemma lem5150094 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term38 s a x).
Proof. exact (eq_refl (term38 s a x)). Qed.
Lemma lem5150095 (P : real -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5150096 (s : real -> Prop) (a : real) : (term51 s a) = (term52 s a).
Proof. exact (@lem5150095 (term39 s a)). Qed.
Lemma lem5150097 (s : real -> Prop) (a : real) (x : real) : (term53 s a x) = (term38 s a x).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5150098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5150099 (s : real -> Prop) (a : real) (x : real) : (term54 s a x) = (term47 s a x).
Proof. exact (MK_COMB (@lem5150098) (@lem5150097 s a x)). Qed.
Lemma lem5150100 (s : real -> Prop) (a : real) (x : real) : (term54 s a x) = (term48 s a x).
Proof. exact (TRANS (@lem5150099 s a x) (@lem5150091 s a x)). Qed.
Lemma lem5150101 (s : real -> Prop) (a : real) : (term55 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5150100 s a x)). Qed.
Lemma lem5150102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150103 (s : real -> Prop) (a : real) : (term52 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5150102) (@lem5150101 s a)). Qed.
Lemma lem5150104 (s : real -> Prop) (a : real) : (term51 s a) = (term57 s a).
Proof. exact (TRANS (@lem5150096 s a) (@lem5150103 s a)). Qed.
Lemma lem5150105 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5150094 s a x)). Qed.
Lemma lem5150106 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150107 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5150106) (@lem5150105 s a)). Qed.
Lemma lem5150109 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5150110 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5150109 a s) (@lem5150107 s a)). Qed.
Lemma lem5150112 (a : real) (s : real -> Prop) : (term60 a s) = (term60 a s).
Proof. exact (eq_refl (term60 a s)). Qed.
Lemma lem5150113 (s : real -> Prop) (a : real) : (term61 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5150112 a s) (@lem5150104 s a)). Qed.
Lemma lem5150114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150115 (s : real -> Prop) (a : real) : (term63 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5150114) (@lem5150113 s a)). Qed.
Lemma lem5150116 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5150115 s a) (@lem5150110 s a)). Qed.
Lemma lem5150117 (s : real -> Prop) (a : real) : (term67 s a) = (term65 s a).
Proof. exact (@lem17646 (term42 a s) (term40 s a)). Qed.
Lemma lem5150118 (s : real -> Prop) (a : real) : (term67 s a) = (term66 s a).
Proof. exact (TRANS (@lem5150117 s a) (@lem5150116 s a)). Qed.
Lemma lem5150120 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150121 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5150120 s) (@lem5150118 s a)). Qed.
Lemma lem5150122 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17362 (term72 s) ((term42 a s) = (term40 s a))). Qed.
Lemma lem5150123 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5150122 s a) (@lem5150121 s a)). Qed.
Lemma lem5150124 (P : real -> Prop) : (term73 P) = (term74 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5150125 (s : real -> Prop) : (term75 s) = (term76 s).
Proof. exact (@lem5150124 (term44 s)). Qed.
Lemma lem5150126 (s : real -> Prop) (a : real) : (term77 s a) = (term43 s a).
Proof. exact (eq_refl (term77 s a)). Qed.
Lemma lem5150127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5150128 (s : real -> Prop) (a : real) : (term78 s a) = (term71 s a).
Proof. exact (MK_COMB (@lem5150127) (@lem5150126 s a)). Qed.
Lemma lem5150129 (s : real -> Prop) (a : real) : (term78 s a) = (term70 s a).
Proof. exact (TRANS (@lem5150128 s a) (@lem5150123 s a)). Qed.
Lemma lem5150130 (s : real -> Prop) : (term79 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5150129 s a)). Qed.
Lemma lem5150131 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150132 (s : real -> Prop) : (term76 s) = (term81 s).
Proof. exact (MK_COMB (@lem5150131) (@lem5150130 s)). Qed.
Lemma lem5150133 (s : real -> Prop) : (term75 s) = (term81 s).
Proof. exact (TRANS (@lem5150125 s) (@lem5150132 s)). Qed.
Lemma lem5150134 (P : type1022) : (term82 P) = (term83 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5150135 : term10 = term84.
Proof. exact (@lem5150134 term46). Qed.
Lemma lem5150136 (s : real -> Prop) : (term85 s) = (term45 s).
Proof. exact (eq_refl (term85 s)). Qed.
Lemma lem5150137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5150138 (s : real -> Prop) : (term86 s) = (term75 s).
Proof. exact (MK_COMB (@lem5150137) (@lem5150136 s)). Qed.
Lemma lem5150139 (s : real -> Prop) : (term86 s) = (term81 s).
Proof. exact (TRANS (@lem5150138 s) (@lem5150133 s)). Qed.
Lemma lem5150140 : term87 = term88.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5150139 s)). Qed.
Lemma lem5150141 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5150142 : term84 = term89.
Proof. exact (MK_COMB (@lem5150141) (@lem5150140)). Qed.
Lemma lem5150143 : term10 = term89.
Proof. exact (TRANS (@lem5150135) (@lem5150142)). Qed.
Lemma lem5150149 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5150150 (P : Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem5150149 real P Q). Qed.
Lemma lem5150151 (s : real -> Prop) : (term94 s) = (term95 s).
Proof. exact (@lem5150150 (term72 s) (term96 s)). Qed.
Lemma lem5150152 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5150153 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150154 (s : real -> Prop) (a : real) : (term98 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5150153 s) (@lem5150152 s a)). Qed.
Lemma lem5150155 (s : real -> Prop) : (term99 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5150154 s a)). Qed.
Lemma lem5150156 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150157 (s : real -> Prop) : (term94 s) = (term81 s).
Proof. exact (MK_COMB (@lem5150156) (@lem5150155 s)). Qed.
Lemma lem5150158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150159 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem5150158) (@lem5150157 s)). Qed.
Lemma lem5150160 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5150161 (s : real -> Prop) : (term102 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5150160 s a)). Qed.
Lemma lem5150162 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150163 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5150162) (@lem5150161 s)). Qed.
Lemma lem5150164 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150165 (s : real -> Prop) : (term95 s) = (term105 s).
Proof. exact (MK_COMB (@lem5150164 s) (@lem5150163 s)). Qed.
Lemma lem5150166 (s : real -> Prop) : ((term94 s) = (term95 s)) = ((term81 s) = (term105 s)).
Proof. exact (MK_COMB (@lem5150159 s) (@lem5150165 s)). Qed.
Lemma lem5150167 (s : real -> Prop) : (term81 s) = (term105 s).
Proof. exact (EQ_MP (@lem5150166 s) (@lem5150151 s)). Qed.
Lemma lem5150169 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5150170 (P : real -> Prop) (Q : real -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem5150169 real P Q). Qed.
Lemma lem5150171 (s : real -> Prop) : (term110 s) = (term111 s).
Proof. exact (@lem5150170 (term112 s) (term113 s)). Qed.
Lemma lem5150172 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5150173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150174 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5150173) (@lem5150172 s a)). Qed.
Lemma lem5150175 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5150176 (s : real -> Prop) (a : real) : (term117 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5150174 s a) (@lem5150175 s a)). Qed.
Lemma lem5150177 (s : real -> Prop) : (term118 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5150176 s a)). Qed.
Lemma lem5150178 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150179 (s : real -> Prop) : (term110 s) = (term104 s).
Proof. exact (MK_COMB (@lem5150178) (@lem5150177 s)). Qed.
Lemma lem5150180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150181 (s : real -> Prop) : (term119 s) = (term120 s).
Proof. exact (MK_COMB (@lem5150180) (@lem5150179 s)). Qed.
Lemma lem5150182 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5150183 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5150182 s a)). Qed.
Lemma lem5150184 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150185 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5150184) (@lem5150183 s)). Qed.
Lemma lem5150186 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150187 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5150186) (@lem5150185 s)). Qed.
Lemma lem5150188 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5150189 (s : real -> Prop) : (term126 s) = (term113 s).
Proof. exact (fun_ext (fun a : real => @lem5150188 s a)). Qed.
Lemma lem5150190 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150191 (s : real -> Prop) : (term127 s) = (term128 s).
Proof. exact (MK_COMB (@lem5150190) (@lem5150189 s)). Qed.
Lemma lem5150192 (s : real -> Prop) : (term111 s) = (term129 s).
Proof. exact (MK_COMB (@lem5150187 s) (@lem5150191 s)). Qed.
Lemma lem5150193 (s : real -> Prop) : ((term110 s) = (term111 s)) = ((term104 s) = (term129 s)).
Proof. exact (MK_COMB (@lem5150181 s) (@lem5150192 s)). Qed.
Lemma lem5150194 (s : real -> Prop) : (term104 s) = (term129 s).
Proof. exact (EQ_MP (@lem5150193 s) (@lem5150171 s)). Qed.
Lemma lem5150387 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150388 (s : real -> Prop) : (term105 s) = (term130 s).
Proof. exact (MK_COMB (@lem5150387 s) (@lem5150194 s)). Qed.
Lemma lem5150389 (s : real -> Prop) : (term81 s) = (term130 s).
Proof. exact (TRANS (@lem5150167 s) (@lem5150388 s)). Qed.
Lemma lem5150390 : term88 = term131.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5150389 s)). Qed.
Lemma lem5150391 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5150392 : term89 = term132.
Proof. exact (MK_COMB (@lem5150391) (@lem5150390)). Qed.
Lemma lem5150442 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5150443 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5150442 real P Q). Qed.
Lemma lem5150444 (s : real -> Prop) (a : real) : (term133 s a) = (term134 s a).
Proof. exact (@lem5150443 (term135 a s) (term39 s a)). Qed.
Lemma lem5150445 (s : real -> Prop) (a : real) (x : real) : (term53 s a x) = (term38 s a x).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5150446 (s : real -> Prop) (a : real) : (term136 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5150445 s a x)). Qed.
Lemma lem5150447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150448 (s : real -> Prop) (a : real) : (term137 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5150447) (@lem5150446 s a)). Qed.
Lemma lem5150449 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5150450 (s : real -> Prop) (a : real) : (term133 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5150449 a s) (@lem5150448 s a)). Qed.
Lemma lem5150451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150452 (s : real -> Prop) (a : real) : (term138 s a) = (term139 s a).
Proof. exact (MK_COMB (@lem5150451) (@lem5150450 s a)). Qed.
Lemma lem5150453 (s : real -> Prop) (a : real) (x : real) : (term53 s a x) = (term38 s a x).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5150454 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5150455 (s : real -> Prop) (a : real) (x : real) : (term140 s a x) = (term141 s a x).
Proof. exact (MK_COMB (@lem5150454 a s) (@lem5150453 s a x)). Qed.
Lemma lem5150456 (s : real -> Prop) (a : real) : (term142 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5150455 s a x)). Qed.
Lemma lem5150457 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150458 (s : real -> Prop) (a : real) : (term134 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5150457) (@lem5150456 s a)). Qed.
Lemma lem5150459 (s : real -> Prop) (a : real) : ((term133 s a) = (term134 s a)) = ((term59 s a) = (term144 s a)).
Proof. exact (MK_COMB (@lem5150452 s a) (@lem5150458 s a)). Qed.
Lemma lem5150460 (s : real -> Prop) (a : real) : (term59 s a) = (term144 s a).
Proof. exact (EQ_MP (@lem5150459 s a) (@lem5150444 s a)). Qed.
Lemma lem5150461 (s : real -> Prop) : (term113 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5150460 s a)). Qed.
Lemma lem5150462 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150463 (s : real -> Prop) : (term128 s) = (term146 s).
Proof. exact (MK_COMB (@lem5150462) (@lem5150461 s)). Qed.
Lemma lem5150464 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (eq_refl (term125 s)). Qed.
Lemma lem5150465 (s : real -> Prop) : (term129 s) = (term147 s).
Proof. exact (MK_COMB (@lem5150464 s) (@lem5150463 s)). Qed.
Lemma lem5150467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5150468 (P : real -> Prop) (Q : real -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem5150467 real P Q). Qed.
Lemma lem5150469 (s : real -> Prop) : (term148 s) = (term149 s).
Proof. exact (@lem5150468 (term112 s) (term145 s)). Qed.
Lemma lem5150470 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5150471 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5150470 s a)). Qed.
Lemma lem5150472 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150473 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5150472) (@lem5150471 s)). Qed.
Lemma lem5150474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150475 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5150474) (@lem5150473 s)). Qed.
Lemma lem5150476 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5150477 (s : real -> Prop) : (term151 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5150476 s a)). Qed.
Lemma lem5150478 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150479 (s : real -> Prop) : (term152 s) = (term146 s).
Proof. exact (MK_COMB (@lem5150478) (@lem5150477 s)). Qed.
Lemma lem5150480 (s : real -> Prop) : (term148 s) = (term147 s).
Proof. exact (MK_COMB (@lem5150475 s) (@lem5150479 s)). Qed.
Lemma lem5150481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150482 (s : real -> Prop) : (term153 s) = (term154 s).
Proof. exact (MK_COMB (@lem5150481) (@lem5150480 s)). Qed.
Lemma lem5150483 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5150484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150485 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5150484) (@lem5150483 s a)). Qed.
Lemma lem5150486 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5150487 (s : real -> Prop) (a : real) : (term155 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5150485 s a) (@lem5150486 s a)). Qed.
Lemma lem5150488 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (fun_ext (fun a : real => @lem5150487 s a)). Qed.
Lemma lem5150489 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150490 (s : real -> Prop) : (term149 s) = (term159 s).
Proof. exact (MK_COMB (@lem5150489) (@lem5150488 s)). Qed.
Lemma lem5150491 (s : real -> Prop) : ((term148 s) = (term149 s)) = ((term147 s) = (term159 s)).
Proof. exact (MK_COMB (@lem5150482 s) (@lem5150490 s)). Qed.
Lemma lem5150492 (s : real -> Prop) : (term147 s) = (term159 s).
Proof. exact (EQ_MP (@lem5150491 s) (@lem5150469 s)). Qed.
Lemma lem5150494 {A : Type'} (P : Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5150495 (P : Prop) (Q : real -> Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem5150494 real P Q). Qed.
Lemma lem5150496 (s : real -> Prop) (a : real) : (term164 s a) = (term165 s a).
Proof. exact (@lem5150495 (term62 s a) (term143 s a)). Qed.
Lemma lem5150497 (s : real -> Prop) (a : real) (x : real) : (term166 s a x) = (term141 s a x).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5150498 (s : real -> Prop) (a : real) : (term167 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5150497 s a x)). Qed.
Lemma lem5150499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150500 (s : real -> Prop) (a : real) : (term168 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5150499) (@lem5150498 s a)). Qed.
Lemma lem5150501 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5150502 (s : real -> Prop) (a : real) : (term164 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5150501 s a) (@lem5150500 s a)). Qed.
Lemma lem5150503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150504 (s : real -> Prop) (a : real) : (term169 s a) = (term170 s a).
Proof. exact (MK_COMB (@lem5150503) (@lem5150502 s a)). Qed.
Lemma lem5150505 (s : real -> Prop) (a : real) (x : real) : (term166 s a x) = (term141 s a x).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5150506 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5150507 (s : real -> Prop) (a : real) (x : real) : (term171 s a x) = (term172 s a x).
Proof. exact (MK_COMB (@lem5150506 s a) (@lem5150505 s a x)). Qed.
Lemma lem5150508 (s : real -> Prop) (a : real) : (term173 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5150507 s a x)). Qed.
Lemma lem5150509 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150510 (s : real -> Prop) (a : real) : (term165 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5150509) (@lem5150508 s a)). Qed.
Lemma lem5150511 (s : real -> Prop) (a : real) : ((term164 s a) = (term165 s a)) = ((term156 s a) = (term175 s a)).
Proof. exact (MK_COMB (@lem5150504 s a) (@lem5150510 s a)). Qed.
Lemma lem5150512 (s : real -> Prop) (a : real) : (term156 s a) = (term175 s a).
Proof. exact (EQ_MP (@lem5150511 s a) (@lem5150496 s a)). Qed.
Lemma lem5150513 (s : real -> Prop) : (term158 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5150512 s a)). Qed.
Lemma lem5150514 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150515 (s : real -> Prop) : (term159 s) = (term177 s).
Proof. exact (MK_COMB (@lem5150514) (@lem5150513 s)). Qed.
Lemma lem5150516 (s : real -> Prop) : (term147 s) = (term177 s).
Proof. exact (TRANS (@lem5150492 s) (@lem5150515 s)). Qed.
Lemma lem5150517 (s : real -> Prop) : (term129 s) = (term177 s).
Proof. exact (TRANS (@lem5150465 s) (@lem5150516 s)). Qed.
Lemma lem5150518 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150519 (s : real -> Prop) : (term130 s) = (term178 s).
Proof. exact (MK_COMB (@lem5150518 s) (@lem5150517 s)). Qed.
Lemma lem5150521 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5150522 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5150521 real P Q). Qed.
Lemma lem5150523 (s : real -> Prop) : (term179 s) = (term180 s).
Proof. exact (@lem5150522 (term72 s) (term176 s)). Qed.
Lemma lem5150524 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5150525 (s : real -> Prop) : (term182 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5150524 s a)). Qed.
Lemma lem5150526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150527 (s : real -> Prop) : (term183 s) = (term177 s).
Proof. exact (MK_COMB (@lem5150526) (@lem5150525 s)). Qed.
Lemma lem5150528 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150529 (s : real -> Prop) : (term179 s) = (term178 s).
Proof. exact (MK_COMB (@lem5150528 s) (@lem5150527 s)). Qed.
Lemma lem5150530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150531 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5150530) (@lem5150529 s)). Qed.
Lemma lem5150532 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5150533 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150534 (s : real -> Prop) (a : real) : (term186 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5150533 s) (@lem5150532 s a)). Qed.
Lemma lem5150535 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun a : real => @lem5150534 s a)). Qed.
Lemma lem5150536 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150537 (s : real -> Prop) : (term180 s) = (term190 s).
Proof. exact (MK_COMB (@lem5150536) (@lem5150535 s)). Qed.
Lemma lem5150538 (s : real -> Prop) : ((term179 s) = (term180 s)) = ((term178 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5150531 s) (@lem5150537 s)). Qed.
Lemma lem5150539 (s : real -> Prop) : (term178 s) = (term190 s).
Proof. exact (EQ_MP (@lem5150538 s) (@lem5150523 s)). Qed.
Lemma lem5150541 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5150542 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5150541 real P Q). Qed.
Lemma lem5150543 (s : real -> Prop) (a : real) : (term191 s a) = (term192 s a).
Proof. exact (@lem5150542 (term72 s) (term174 s a)). Qed.
Lemma lem5150544 (s : real -> Prop) (a : real) (x : real) : (term193 s a x) = (term172 s a x).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5150545 (s : real -> Prop) (a : real) : (term194 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5150544 s a x)). Qed.
Lemma lem5150546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150547 (s : real -> Prop) (a : real) : (term195 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5150546) (@lem5150545 s a)). Qed.
Lemma lem5150548 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150549 (s : real -> Prop) (a : real) : (term191 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5150548 s) (@lem5150547 s a)). Qed.
Lemma lem5150550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150551 (s : real -> Prop) (a : real) : (term196 s a) = (term197 s a).
Proof. exact (MK_COMB (@lem5150550) (@lem5150549 s a)). Qed.
Lemma lem5150552 (s : real -> Prop) (a : real) (x : real) : (term193 s a x) = (term172 s a x).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5150553 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150554 (s : real -> Prop) (a : real) (x : real) : (term198 s a x) = (term199 s a x).
Proof. exact (MK_COMB (@lem5150553 s) (@lem5150552 s a x)). Qed.
Lemma lem5150555 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (fun_ext (fun x : real => @lem5150554 s a x)). Qed.
Lemma lem5150556 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150557 (s : real -> Prop) (a : real) : (term192 s a) = (term202 s a).
Proof. exact (MK_COMB (@lem5150556) (@lem5150555 s a)). Qed.
Lemma lem5150558 (s : real -> Prop) (a : real) : ((term191 s a) = (term192 s a)) = ((term187 s a) = (term202 s a)).
Proof. exact (MK_COMB (@lem5150551 s a) (@lem5150557 s a)). Qed.
Lemma lem5150559 (s : real -> Prop) (a : real) : (term187 s a) = (term202 s a).
Proof. exact (EQ_MP (@lem5150558 s a) (@lem5150543 s a)). Qed.
Lemma lem5150560 (s : real -> Prop) : (term189 s) = (term203 s).
Proof. exact (fun_ext (fun a : real => @lem5150559 s a)). Qed.
Lemma lem5150561 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5150562 (s : real -> Prop) : (term190 s) = (term204 s).
Proof. exact (MK_COMB (@lem5150561) (@lem5150560 s)). Qed.
Lemma lem5150563 (s : real -> Prop) : (term178 s) = (term204 s).
Proof. exact (TRANS (@lem5150539 s) (@lem5150562 s)). Qed.
Lemma lem5150564 (s : real -> Prop) : (term130 s) = (term204 s).
Proof. exact (TRANS (@lem5150519 s) (@lem5150563 s)). Qed.
Lemma lem5150565 : term131 = term205.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5150564 s)). Qed.
Lemma lem5150566 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5150567 : term132 = term206.
Proof. exact (MK_COMB (@lem5150566) (@lem5150565)). Qed.
Lemma lem5150568 : term89 = term206.
Proof. exact (TRANS (@lem5150392) (@lem5150567)). Qed.
Lemma lem5150569 : term10 = term206.
Proof. exact (TRANS (@lem5150143) (@lem5150568)). Qed.
Lemma lem5150570 (h1 : term10) : term206.
Proof. exact (EQ_MP (@lem5150569) (@lem5150073 h1)). Qed.
Lemma lem5150577 (x : real) (y : real) (z : real) : (term207 x y z) = (term208 x y z).
Proof. exact (@lem17045 (real_lt x y) (real_le y z)). Qed.
Lemma lem5150578 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem5150579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150580 (x : real) (y : real) (z : real) : (term209 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem5150579) (@lem5150577 x y z)). Qed.
Lemma lem5150581 (y : real) (x : real) (z : real) : (term211 y x z) = (term212 y x z).
Proof. exact (MK_COMB (@lem5150580 x y z) (@lem5150578 x z)). Qed.
Lemma lem5150582 (y : real) (x : real) (z : real) : (term31 y x z) = (term211 y x z).
Proof. exact (@lem17265 (term213 x y z) (real_lt x z)). Qed.
Lemma lem5150583 (y : real) (x : real) (z : real) : (term31 y x z) = (term212 y x z).
Proof. exact (TRANS (@lem5150582 y x z) (@lem5150581 y x z)). Qed.
Lemma lem5150584 (y : real) (x : real) : (term32 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5150583 y x z)). Qed.
Lemma lem5150585 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150586 (y : real) (x : real) : (term33 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5150585) (@lem5150584 y x)). Qed.
Lemma lem5150587 (x : real) : (term34 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5150586 y x)). Qed.
Lemma lem5150588 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150589 (x : real) : (term35 x) = (term217 x).
Proof. exact (MK_COMB (@lem5150588) (@lem5150587 x)). Qed.
Lemma lem5150590 : term36 = term218.
Proof. exact (fun_ext (fun x : real => @lem5150589 x)). Qed.
Lemma lem5150591 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150652 : term37 = term219.
Proof. exact (MK_COMB (@lem5150591) (@lem5150590)). Qed.
Lemma lem5150653 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5150652) (@lem5150074 h1)). Qed.
Lemma lem5150657 (s : real -> Prop) : (term220 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5150659 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5150660 (s : real -> Prop) : (term222 s) = (term223 s).
Proof. exact (MK_COMB (@lem5150659 s) (@lem5150657 s)). Qed.
Lemma lem5150661 (s : real -> Prop) : (term224 s) = (term222 s).
Proof. exact (@lem17045 (@FINITE real s) (term225 s)). Qed.
Lemma lem5150662 (s : real -> Prop) : (term224 s) = (term223 s).
Proof. exact (TRANS (@lem5150661 s) (@lem5150660 s)). Qed.
Lemma lem5150670 (x : real) (s : real -> Prop) : (term23 x s) = (term226 x s).
Proof. exact (@lem17265 (@IN real x s) (term227 x s)). Qed.
Lemma lem5150671 (s : real -> Prop) : (term24 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5150670 x s)). Qed.
Lemma lem5150672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150673 (s : real -> Prop) : (term25 s) = (term229 s).
Proof. exact (MK_COMB (@lem5150672) (@lem5150671 s)). Qed.
Lemma lem5150675 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5150676 (s : real -> Prop) : (term27 s) = (term230 s).
Proof. exact (MK_COMB (@lem5150675 s) (@lem5150673 s)). Qed.
Lemma lem5150677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150678 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (MK_COMB (@lem5150677) (@lem5150662 s)). Qed.
Lemma lem5150679 (s : real -> Prop) : (term233 s) = (term234 s).
Proof. exact (MK_COMB (@lem5150678 s) (@lem5150676 s)). Qed.
Lemma lem5150680 (s : real -> Prop) : (term29 s) = (term233 s).
Proof. exact (@lem17265 (term72 s) (term27 s)). Qed.
Lemma lem5150681 (s : real -> Prop) : (term29 s) = (term234 s).
Proof. exact (TRANS (@lem5150680 s) (@lem5150679 s)). Qed.
Lemma lem5150682 : term30 = term235.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5150681 s)). Qed.
Lemma lem5150683 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5150784 : term17 = term236.
Proof. exact (MK_COMB (@lem5150683) (@lem5150682)). Qed.
Lemma lem5150785 (h1 : term17) : term236.
Proof. exact (EQ_MP (@lem5150784) (@lem5150075 h1)). Qed.
Lemma lem5150786 (s : real -> Prop) (h1 : term204 s) : term204 s.
Proof. exact (h1). Qed.
Lemma lem5150787 (s : real -> Prop) (a : real) (h1 : term202 s a) : term202 s a.
Proof. exact (h1). Qed.
Lemma lem5150788 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term199 s a x.
Proof. exact (h1). Qed.
Lemma lem5150813 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5150814 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5150813 y x z)). Qed.
Lemma lem5150815 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150816 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5150815) (@lem5150814 y x)). Qed.
Lemma lem5150817 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5150816 y x)). Qed.
Lemma lem5150818 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150819 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5150818) (@lem5150817 x)). Qed.
Lemma lem5150820 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5150819 x)). Qed.
Lemma lem5150821 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150822 : term219 = term219.
Proof. exact (MK_COMB (@lem5150821) (@lem5150820)). Qed.
Lemma lem5150823 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5150822) (@lem5150653 h1)). Qed.
Lemma lem5150840 (x : real) (s : real -> Prop) : (term226 x s) = (term226 x s).
Proof. exact (eq_refl (term226 x s)). Qed.
Lemma lem5150841 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5150840 x s)). Qed.
Lemma lem5150842 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150843 (s : real -> Prop) : (term229 s) = (term229 s).
Proof. exact (MK_COMB (@lem5150842) (@lem5150841 s)). Qed.
Lemma lem5150852 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5150853 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (MK_COMB (@lem5150852 s) (@lem5150843 s)). Qed.
Lemma lem5150868 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5150869 (s : real -> Prop) : (term234 s) = (term234 s).
Proof. exact (MK_COMB (@lem5150868 s) (@lem5150853 s)). Qed.
Lemma lem5150870 : term235 = term235.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5150869 s)). Qed.
Lemma lem5150871 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5150872 : term236 = term236.
Proof. exact (MK_COMB (@lem5150871) (@lem5150870)). Qed.
Lemma lem5150873 (h1 : term17) : term236.
Proof. exact (EQ_MP (@lem5150872) (@lem5150785 h1)). Qed.
Lemma lem5150898 (s : real -> Prop) (a : real) (x : real) : (term141 s a x) = (term141 s a x).
Proof. exact (eq_refl (term141 s a x)). Qed.
Lemma lem5150915 (s : real -> Prop) (a : real) (x : real) : (term48 s a x) = (term48 s a x).
Proof. exact (eq_refl (term48 s a x)). Qed.
Lemma lem5150916 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5150915 s a x)). Qed.
Lemma lem5150917 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150918 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5150917) (@lem5150916 s a)). Qed.
Lemma lem5150927 (a : real) (s : real -> Prop) : (term60 a s) = (term60 a s).
Proof. exact (eq_refl (term60 a s)). Qed.
Lemma lem5150928 (s : real -> Prop) (a : real) : (term62 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5150927 a s) (@lem5150918 s a)). Qed.
Lemma lem5150929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5150930 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5150929) (@lem5150928 s a)). Qed.
Lemma lem5150931 (s : real -> Prop) (a : real) (x : real) : (term172 s a x) = (term172 s a x).
Proof. exact (MK_COMB (@lem5150930 s a) (@lem5150898 s a x)). Qed.
Lemma lem5150946 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5150947 (s : real -> Prop) (a : real) (x : real) : (term199 s a x) = (term199 s a x).
Proof. exact (MK_COMB (@lem5150946 s) (@lem5150931 s a x)). Qed.
Lemma lem5150948 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term199 s a x.
Proof. exact (EQ_MP (@lem5150947 s a x) (@lem5150788 s a x h1)). Qed.
Lemma lem5150949 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term172 s a x.
Proof. exact (proj2 (@lem5150948 s a x h1)). Qed.
Lemma lem5150950 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term72 s.
Proof. exact (proj1 (@lem5150948 s a x h1)). Qed.
Lemma lem5150953 (s : real -> Prop) (a : real) (h1 : term62 s a) : term62 s a.
Proof. exact (h1). Qed.
Lemma lem5150954 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term141 s a x.
Proof. exact (h1). Qed.
Lemma lem5150955 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (proj2 (@lem5150953 s a h1)). Qed.
Lemma lem5150957 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term38 s a x.
Proof. exact (proj2 (@lem5150954 s a x h1)). Qed.
Lemma lem5150987 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5150988 (P : Prop) (Q : real -> Prop) : (term239 P Q) = (term240 P Q).
Proof. exact (@lem5150987 real P Q). Qed.
Lemma lem5150989 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (@lem5150988 (term243 s) (term228 s)). Qed.
Lemma lem5150990 (x : real) (s : real -> Prop) : (term244 s x) = (term226 x s).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5150991 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5150990 x s)). Qed.
Lemma lem5150992 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5150993 (s : real -> Prop) : (term246 s) = (term229 s).
Proof. exact (MK_COMB (@lem5150992) (@lem5150991 s)). Qed.
Lemma lem5150994 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5150995 (s : real -> Prop) : (term241 s) = (term230 s).
Proof. exact (MK_COMB (@lem5150994 s) (@lem5150993 s)). Qed.
Lemma lem5150996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5150997 (s : real -> Prop) : (term247 s) = (term248 s).
Proof. exact (MK_COMB (@lem5150996) (@lem5150995 s)). Qed.
Lemma lem5150998 (x : real) (s : real -> Prop) : (term244 s x) = (term226 x s).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5150999 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5151000 (x : real) (s : real -> Prop) : (term249 s x) = (term250 x s).
Proof. exact (MK_COMB (@lem5150999 s) (@lem5150998 x s)). Qed.
Lemma lem5151001 (s : real -> Prop) : (term251 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5151000 x s)). Qed.
Lemma lem5151002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151003 (s : real -> Prop) : (term242 s) = (term253 s).
Proof. exact (MK_COMB (@lem5151002) (@lem5151001 s)). Qed.
Lemma lem5151004 (s : real -> Prop) : ((term241 s) = (term242 s)) = ((term230 s) = (term253 s)).
Proof. exact (MK_COMB (@lem5150997 s) (@lem5151003 s)). Qed.
Lemma lem5151005 (s : real -> Prop) : (term230 s) = (term253 s).
Proof. exact (EQ_MP (@lem5151004 s) (@lem5150989 s)). Qed.
Lemma lem5151006 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5151007 (s : real -> Prop) : (term234 s) = (term254 s).
Proof. exact (MK_COMB (@lem5151006 s) (@lem5151005 s)). Qed.
Lemma lem5151009 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5151010 (P : Prop) (Q : real -> Prop) : (term257 P Q) = (term258 P Q).
Proof. exact (@lem5151009 real P Q). Qed.
Lemma lem5151011 (s : real -> Prop) : (term259 s) = (term260 s).
Proof. exact (@lem5151010 (term223 s) (term252 s)). Qed.
Lemma lem5151012 (x : real) (s : real -> Prop) : (term261 s x) = (term250 x s).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5151013 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5151012 x s)). Qed.
Lemma lem5151014 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151015 (s : real -> Prop) : (term263 s) = (term253 s).
Proof. exact (MK_COMB (@lem5151014) (@lem5151013 s)). Qed.
Lemma lem5151016 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5151017 (s : real -> Prop) : (term259 s) = (term254 s).
Proof. exact (MK_COMB (@lem5151016 s) (@lem5151015 s)). Qed.
Lemma lem5151018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5151019 (s : real -> Prop) : (term264 s) = (term265 s).
Proof. exact (MK_COMB (@lem5151018) (@lem5151017 s)). Qed.
Lemma lem5151020 (x : real) (s : real -> Prop) : (term261 s x) = (term250 x s).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5151021 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5151022 (x : real) (s : real -> Prop) : (term266 s x) = (term267 x s).
Proof. exact (MK_COMB (@lem5151021 s) (@lem5151020 x s)). Qed.
Lemma lem5151023 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (fun_ext (fun x : real => @lem5151022 x s)). Qed.
Lemma lem5151024 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151025 (s : real -> Prop) : (term260 s) = (term270 s).
Proof. exact (MK_COMB (@lem5151024) (@lem5151023 s)). Qed.
Lemma lem5151026 (s : real -> Prop) : ((term259 s) = (term260 s)) = ((term254 s) = (term270 s)).
Proof. exact (MK_COMB (@lem5151019 s) (@lem5151025 s)). Qed.
Lemma lem5151027 (s : real -> Prop) : (term254 s) = (term270 s).
Proof. exact (EQ_MP (@lem5151026 s) (@lem5151011 s)). Qed.
Lemma lem5151028 (s : real -> Prop) : (term234 s) = (term270 s).
Proof. exact (TRANS (@lem5151007 s) (@lem5151027 s)). Qed.
Lemma lem5151029 : term235 = term271.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5151028 s)). Qed.
Lemma lem5151030 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5151031 : term236 = term272.
Proof. exact (MK_COMB (@lem5151030) (@lem5151029)). Qed.
Lemma lem5151060 (x : real) (s : real -> Prop) : (term267 x s) = (term273 x s).
Proof. exact (@lem19490 (term243 s) (term223 s) (term226 x s)). Qed.
Lemma lem5151061 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (fun_ext (fun x : real => @lem5151060 x s)). Qed.
Lemma lem5151062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151063 (s : real -> Prop) : (term270 s) = (term275 s).
Proof. exact (MK_COMB (@lem5151062) (@lem5151061 s)). Qed.
Lemma lem5151064 : term271 = term276.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5151063 s)). Qed.
Lemma lem5151065 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5151066 : term272 = term277.
Proof. exact (MK_COMB (@lem5151065) (@lem5151064)). Qed.
Lemma lem5151067 : term236 = term277.
Proof. exact (TRANS (@lem5151031) (@lem5151066)). Qed.
Lemma lem5151068 (h1 : term17) : term277.
Proof. exact (EQ_MP (@lem5151067) (@lem5150873 h1)). Qed.
Lemma lem5151088 (s : real -> Prop) (a : real) (x : real) : (term48 s a x) = (term48 s a x).
Proof. exact (eq_refl (term48 s a x)). Qed.
Lemma lem5151089 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5151088 s a x)). Qed.
Lemma lem5151090 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151092 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5151090) (@lem5151089 s a)). Qed.
Lemma lem5151093 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (EQ_MP (@lem5151092 s a) (@lem5150955 s a h1)). Qed.
Lemma lem5151107 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5151108 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5151107 y x z)). Qed.
Lemma lem5151109 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151110 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5151109) (@lem5151108 y x)). Qed.
Lemma lem5151111 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5151110 y x)). Qed.
Lemma lem5151112 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151113 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5151112) (@lem5151111 x)). Qed.
Lemma lem5151114 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5151113 x)). Qed.
Lemma lem5151115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151117 : term219 = term219.
Proof. exact (MK_COMB (@lem5151115) (@lem5151114)). Qed.
Lemma lem5151118 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5151117) (@lem5150823 h1)). Qed.
Lemma lem5151120 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5151121 (P : Prop) (Q : real -> Prop) : (term239 P Q) = (term240 P Q).
Proof. exact (@lem5151120 real P Q). Qed.
Lemma lem5151122 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (@lem5151121 (term243 s) (term228 s)). Qed.
Lemma lem5151123 (x : real) (s : real -> Prop) : (term244 s x) = (term226 x s).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5151124 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5151123 x s)). Qed.
Lemma lem5151125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151126 (s : real -> Prop) : (term246 s) = (term229 s).
Proof. exact (MK_COMB (@lem5151125) (@lem5151124 s)). Qed.
Lemma lem5151127 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5151128 (s : real -> Prop) : (term241 s) = (term230 s).
Proof. exact (MK_COMB (@lem5151127 s) (@lem5151126 s)). Qed.
Lemma lem5151129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5151130 (s : real -> Prop) : (term247 s) = (term248 s).
Proof. exact (MK_COMB (@lem5151129) (@lem5151128 s)). Qed.
Lemma lem5151131 (x : real) (s : real -> Prop) : (term244 s x) = (term226 x s).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5151132 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5151133 (x : real) (s : real -> Prop) : (term249 s x) = (term250 x s).
Proof. exact (MK_COMB (@lem5151132 s) (@lem5151131 x s)). Qed.
Lemma lem5151134 (s : real -> Prop) : (term251 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5151133 x s)). Qed.
Lemma lem5151135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151136 (s : real -> Prop) : (term242 s) = (term253 s).
Proof. exact (MK_COMB (@lem5151135) (@lem5151134 s)). Qed.
Lemma lem5151137 (s : real -> Prop) : ((term241 s) = (term242 s)) = ((term230 s) = (term253 s)).
Proof. exact (MK_COMB (@lem5151130 s) (@lem5151136 s)). Qed.
Lemma lem5151138 (s : real -> Prop) : (term230 s) = (term253 s).
Proof. exact (EQ_MP (@lem5151137 s) (@lem5151122 s)). Qed.
Lemma lem5151139 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5151140 (s : real -> Prop) : (term234 s) = (term254 s).
Proof. exact (MK_COMB (@lem5151139 s) (@lem5151138 s)). Qed.
Lemma lem5151142 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5151143 (P : Prop) (Q : real -> Prop) : (term257 P Q) = (term258 P Q).
Proof. exact (@lem5151142 real P Q). Qed.
Lemma lem5151144 (s : real -> Prop) : (term259 s) = (term260 s).
Proof. exact (@lem5151143 (term223 s) (term252 s)). Qed.
Lemma lem5151145 (x : real) (s : real -> Prop) : (term261 s x) = (term250 x s).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5151146 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5151145 x s)). Qed.
Lemma lem5151147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151148 (s : real -> Prop) : (term263 s) = (term253 s).
Proof. exact (MK_COMB (@lem5151147) (@lem5151146 s)). Qed.
Lemma lem5151149 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5151150 (s : real -> Prop) : (term259 s) = (term254 s).
Proof. exact (MK_COMB (@lem5151149 s) (@lem5151148 s)). Qed.
Lemma lem5151151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5151152 (s : real -> Prop) : (term264 s) = (term265 s).
Proof. exact (MK_COMB (@lem5151151) (@lem5151150 s)). Qed.
Lemma lem5151153 (x : real) (s : real -> Prop) : (term261 s x) = (term250 x s).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5151154 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5151155 (x : real) (s : real -> Prop) : (term266 s x) = (term267 x s).
Proof. exact (MK_COMB (@lem5151154 s) (@lem5151153 x s)). Qed.
Lemma lem5151156 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (fun_ext (fun x : real => @lem5151155 x s)). Qed.
Lemma lem5151157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151158 (s : real -> Prop) : (term260 s) = (term270 s).
Proof. exact (MK_COMB (@lem5151157) (@lem5151156 s)). Qed.
Lemma lem5151159 (s : real -> Prop) : ((term259 s) = (term260 s)) = ((term254 s) = (term270 s)).
Proof. exact (MK_COMB (@lem5151152 s) (@lem5151158 s)). Qed.
Lemma lem5151160 (s : real -> Prop) : (term254 s) = (term270 s).
Proof. exact (EQ_MP (@lem5151159 s) (@lem5151144 s)). Qed.
Lemma lem5151161 (s : real -> Prop) : (term234 s) = (term270 s).
Proof. exact (TRANS (@lem5151140 s) (@lem5151160 s)). Qed.
Lemma lem5151162 : term235 = term271.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5151161 s)). Qed.
Lemma lem5151163 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5151164 : term236 = term272.
Proof. exact (MK_COMB (@lem5151163) (@lem5151162)). Qed.
Lemma lem5151193 (x : real) (s : real -> Prop) : (term267 x s) = (term273 x s).
Proof. exact (@lem19490 (term243 s) (term223 s) (term226 x s)). Qed.
Lemma lem5151194 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (fun_ext (fun x : real => @lem5151193 x s)). Qed.
Lemma lem5151195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5151196 (s : real -> Prop) : (term270 s) = (term275 s).
Proof. exact (MK_COMB (@lem5151195) (@lem5151194 s)). Qed.
Lemma lem5151197 : term271 = term276.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5151196 s)). Qed.
Lemma lem5151198 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5151199 : term272 = term277.
Proof. exact (MK_COMB (@lem5151198) (@lem5151197)). Qed.
Lemma lem5151200 : term236 = term277.
Proof. exact (TRANS (@lem5151164) (@lem5151199)). Qed.
Lemma lem5151201 (h1 : term17) : term277.
Proof. exact (EQ_MP (@lem5151200) (@lem5150873 h1)). Qed.
Lemma lem5151231 (_67249 : real -> Prop) (h1 : term17) : term278 _67249.
Proof. exact (@lem5151068 h1 _67249). Qed.
Lemma lem5151232 (_67249 : real -> Prop) : (term278 _67249) = (term275 _67249).
Proof. exact (eq_refl (term278 _67249)). Qed.
Lemma lem5151233 (_67249 : real -> Prop) (h1 : term17) : term275 _67249.
Proof. exact (EQ_MP (@lem5151232 _67249) (@lem5151231 _67249 h1)). Qed.
Lemma lem5151234 (_67249 : real -> Prop) (_67250 : real) (h1 : term17) : term279 _67249 _67250.
Proof. exact (@lem5151233 _67249 h1 _67250). Qed.
Lemma lem5151235 (_67250 : real) (_67249 : real -> Prop) : (term279 _67249 _67250) = (term273 _67250 _67249).
Proof. exact (eq_refl (term279 _67249 _67250)). Qed.
Lemma lem5151236 (_67250 : real) (_67249 : real -> Prop) (h1 : term17) : term273 _67250 _67249.
Proof. exact (EQ_MP (@lem5151235 _67250 _67249) (@lem5151234 _67249 _67250 h1)). Qed.
Lemma lem5151237 (_67251 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term280 s a _67251.
Proof. exact (@lem5151093 s a h1 _67251). Qed.
Lemma lem5151238 (s : real -> Prop) (a : real) (_67251 : real) : (term280 s a _67251) = (term48 s a _67251).
Proof. exact (eq_refl (term280 s a _67251)). Qed.
Lemma lem5151240 (_67252 : real) (h1 : term37) : term281 _67252.
Proof. exact (@lem5151118 h1 _67252). Qed.
Lemma lem5151241 (_67252 : real) : (term281 _67252) = (term217 _67252).
Proof. exact (eq_refl (term281 _67252)). Qed.
Lemma lem5151242 (_67252 : real) (h1 : term37) : term217 _67252.
Proof. exact (EQ_MP (@lem5151241 _67252) (@lem5151240 _67252 h1)). Qed.
Lemma lem5151243 (_67252 : real) (_67253 : real) (h1 : term37) : term282 _67252 _67253.
Proof. exact (@lem5151242 _67252 h1 _67253). Qed.
Lemma lem5151244 (_67253 : real) (_67252 : real) : (term282 _67252 _67253) = (term215 _67253 _67252).
Proof. exact (eq_refl (term282 _67252 _67253)). Qed.
Lemma lem5151245 (_67253 : real) (_67252 : real) (h1 : term37) : term215 _67253 _67252.
Proof. exact (EQ_MP (@lem5151244 _67253 _67252) (@lem5151243 _67252 _67253 h1)). Qed.
Lemma lem5151246 (_67253 : real) (_67252 : real) (_67254 : real) (h1 : term37) : term283 _67253 _67252 _67254.
Proof. exact (@lem5151245 _67253 _67252 h1 _67254). Qed.
Lemma lem5151247 (_67253 : real) (_67252 : real) (_67254 : real) : (term283 _67253 _67252 _67254) = (term212 _67253 _67252 _67254).
Proof. exact (eq_refl (term283 _67253 _67252 _67254)). Qed.
Lemma lem5151248 (_67253 : real) (_67252 : real) (_67254 : real) (h1 : term37) : term212 _67253 _67252 _67254.
Proof. exact (EQ_MP (@lem5151247 _67253 _67252 _67254) (@lem5151246 _67253 _67252 _67254 h1)). Qed.
Lemma lem5151249 (_67255 : real -> Prop) (h1 : term17) : term278 _67255.
Proof. exact (@lem5151201 h1 _67255). Qed.
Lemma lem5151250 (_67255 : real -> Prop) : (term278 _67255) = (term275 _67255).
Proof. exact (eq_refl (term278 _67255)). Qed.
Lemma lem5151251 (_67255 : real -> Prop) (h1 : term17) : term275 _67255.
Proof. exact (EQ_MP (@lem5151250 _67255) (@lem5151249 _67255 h1)). Qed.
Lemma lem5151252 (_67255 : real -> Prop) (_67256 : real) (h1 : term17) : term279 _67255 _67256.
Proof. exact (@lem5151251 _67255 h1 _67256). Qed.
Lemma lem5151253 (_67256 : real) (_67255 : real -> Prop) : (term279 _67255 _67256) = (term273 _67256 _67255).
Proof. exact (eq_refl (term279 _67255 _67256)). Qed.
Lemma lem5151254 (_67256 : real) (_67255 : real -> Prop) (h1 : term17) : term273 _67256 _67255.
Proof. exact (EQ_MP (@lem5151253 _67256 _67255) (@lem5151252 _67255 _67256 h1)). Qed.
Lemma lem5151256 (_67249 : real -> Prop) (h1 : term17) : term284 _67249.
Proof. exact (proj1 (@lem5151236 (@el real) _67249 h1)). Qed.
Lemma lem5151257 (_67256 : real) (_67255 : real -> Prop) (h1 : term17) : term285 _67256 _67255.
Proof. exact (proj2 (@lem5151254 _67256 _67255 h1)). Qed.
Lemma lem5151274 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term225 s.
Proof. exact (proj2 (@lem5150950 s a x h1)). Qed.
Lemma lem5151282 (_67251 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term48 s a _67251.
Proof. exact (EQ_MP (@lem5151238 s a _67251) (@lem5151237 _67251 s a h1)). Qed.
Lemma lem5151293 (_67249 : real -> Prop) : (term284 _67249) = (term286 _67249).
Proof. exact (@lem5149784 (term287 _67249) (_67249 = (@EMPTY real)) (term243 _67249)). Qed.
Lemma lem5151294 (_67249 : real -> Prop) (h1 : term17) : term286 _67249.
Proof. exact (EQ_MP (@lem5151293 _67249) (@lem5151256 _67249 h1)). Qed.
Lemma lem5151321 (_67253 : real) (_67252 : real) (_67254 : real) : (term212 _67253 _67252 _67254) = (term288 _67253 _67252 _67254).
Proof. exact (@lem5149784 (term289 _67252 _67253) (term290 _67253 _67254) (real_lt _67252 _67254)). Qed.
Lemma lem5151322 (_67253 : real) (_67252 : real) (_67254 : real) (h1 : term37) : term288 _67253 _67252 _67254.
Proof. exact (EQ_MP (@lem5151321 _67253 _67252 _67254) (@lem5151248 _67253 _67252 _67254 h1)). Qed.
Lemma lem5151328 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term135 a s.
Proof. exact (proj1 (@lem5150954 s a x h1)). Qed.
Lemma lem5151359 (_67256 : real) (_67255 : real -> Prop) : (term285 _67256 _67255) = (term291 _67256 _67255).
Proof. exact (@lem5149784 (term287 _67255) (_67255 = (@EMPTY real)) (term226 _67256 _67255)). Qed.
Lemma lem5151360 (_67256 : real) (_67255 : real -> Prop) (h1 : term17) : term291 _67256 _67255.
Proof. exact (EQ_MP (@lem5151359 _67256 _67255) (@lem5151257 _67256 _67255 h1)). Qed.
Lemma lem5151443 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (proj1 (@lem5150950 s a x h1)). Qed.
Lemma lem5151444 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term292 s.
Proof. exact (fun h0 : term287 s => @lem5151443 s a x h1). Qed.
Lemma lem5151446 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151447 (s : real -> Prop) : (term292 s) = (@FINITE real s).
Proof. exact (@lem5151446 (@FINITE real s)). Qed.
Lemma lem5151448 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (EQ_MP (@lem5151447 s) (@lem5151444 s a x h1)). Qed.
Lemma lem5151450 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 a s.
Proof. exact (proj1 (@lem5150953 s a h1)). Qed.
Lemma lem5151451 (s : real -> Prop) (a : real) (h1 : term62 s a) : term294 a s.
Proof. exact (fun h0 : term135 a s => @lem5151450 s a h1). Qed.
Lemma lem5151453 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151454 (a : real) (s : real -> Prop) : (term294 a s) = (term42 a s).
Proof. exact (@lem5151453 (term42 a s)). Qed.
Lemma lem5151455 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 a s.
Proof. exact (EQ_MP (@lem5151454 a s) (@lem5151451 s a h1)). Qed.
Lemma lem5151457 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5151458 (a : real) (_67251 : real) (s : real -> Prop) : (term48 s a _67251) = (term296 a _67251 s).
Proof. exact (@lem5151457 (term289 a _67251) (term297 _67251 s)). Qed.
Lemma lem5151460 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5151461 (a : real) (_67251 : real) : (term299 a _67251) = (real_lt a _67251).
Proof. exact (@lem5151460 (real_lt a _67251)). Qed.
Lemma lem5151462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5151463 (a : real) (_67251 : real) : (term300 a _67251) = (term301 a _67251).
Proof. exact (MK_COMB (@lem5151462) (@lem5151461 a _67251)). Qed.
Lemma lem5151464 (_67251 : real) (s : real -> Prop) : (term297 _67251 s) = (term297 _67251 s).
Proof. exact (eq_refl (term297 _67251 s)). Qed.
Lemma lem5151465 (a : real) (_67251 : real) (s : real -> Prop) : (term296 a _67251 s) = (term302 a _67251 s).
Proof. exact (MK_COMB (@lem5151463 a _67251) (@lem5151464 _67251 s)). Qed.
Lemma lem5151466 (a : real) (_67251 : real) (s : real -> Prop) : (term48 s a _67251) = (term302 a _67251 s).
Proof. exact (TRANS (@lem5151458 a _67251 s) (@lem5151465 a _67251 s)). Qed.
Lemma lem5151469 (_67251 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term302 a _67251 s.
Proof. exact (EQ_MP (@lem5151466 a _67251 s) (@lem5151282 _67251 s a h1)). Qed.
Lemma lem5151470 (s : real -> Prop) (a : real) (h1 : term62 s a) : term303 a s.
Proof. exact (@lem5151469 (sup s) s a h1). Qed.
Lemma lem5151473 (s : real -> Prop) (a : real) (h1 : term62 s a) : term304 s.
Proof. exact (@lem5151470 s a h1 (@lem5151455 s a h1)). Qed.
Lemma lem5151474 (s : real -> Prop) (a : real) (h1 : term62 s a) : term305 s.
Proof. exact (fun h0 : term243 s => @lem5151473 s a h1). Qed.
Lemma lem5151476 (p : Prop) : (term306 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5151477 (s : real -> Prop) : (term305 s) = (term304 s).
Proof. exact (@lem5151476 (term243 s)). Qed.
Lemma lem5151478 (s : real -> Prop) (a : real) (h1 : term62 s a) : term304 s.
Proof. exact (EQ_MP (@lem5151477 s) (@lem5151474 s a h1)). Qed.
Lemma lem5151484 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151485 (_67249 : real -> Prop) : (term286 _67249) = (term307 _67249).
Proof. exact (@lem5151484 (_67249 = (@EMPTY real)) (term287 _67249) (term243 _67249)). Qed.
Lemma lem5151501 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5151502 (_67249 : real -> Prop) : (term308 _67249) = (term309 _67249).
Proof. exact (@lem5151501 (term243 _67249) (term287 _67249)). Qed.
Lemma lem5151508 (_67249 : real -> Prop) : (term310 _67249) = (term310 _67249).
Proof. exact (eq_refl (term310 _67249)). Qed.
Lemma lem5151509 (_67249 : real -> Prop) : (term307 _67249) = (term311 _67249).
Proof. exact (MK_COMB (@lem5151508 _67249) (@lem5151502 _67249)). Qed.
Lemma lem5151520 (_67249 : real -> Prop) : (term286 _67249) = (term311 _67249).
Proof. exact (TRANS (@lem5151485 _67249) (@lem5151509 _67249)). Qed.
Lemma lem5151521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5151522 (_67249 : real -> Prop) : (term312 _67249) = (term313 _67249).
Proof. exact (MK_COMB (@lem5151521) (@lem5151520 _67249)). Qed.
Lemma lem5151538 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5151539 (_67249 : real -> Prop) : (term308 _67249) = (term309 _67249).
Proof. exact (@lem5151538 (term243 _67249) (term287 _67249)). Qed.
Lemma lem5151545 (_67249 : real -> Prop) : (term310 _67249) = (term310 _67249).
Proof. exact (eq_refl (term310 _67249)). Qed.
Lemma lem5151546 (_67249 : real -> Prop) : (term307 _67249) = (term311 _67249).
Proof. exact (MK_COMB (@lem5151545 _67249) (@lem5151539 _67249)). Qed.
Lemma lem5151557 (_67249 : real -> Prop) : ((term286 _67249) = (term307 _67249)) = ((term311 _67249) = (term311 _67249)).
Proof. exact (MK_COMB (@lem5151522 _67249) (@lem5151546 _67249)). Qed.
Lemma lem5151559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5151560 (x : Prop) : (x = x) = True.
Proof. exact (@lem5151559 Prop x). Qed.
Lemma lem5151561 (_67249 : real -> Prop) : ((term311 _67249) = (term311 _67249)) = True.
Proof. exact (@lem5151560 (term311 _67249)). Qed.
Lemma lem5151562 (_67249 : real -> Prop) : ((term286 _67249) = (term307 _67249)) = True.
Proof. exact (TRANS (@lem5151557 _67249) (@lem5151561 _67249)). Qed.
Lemma lem5151563 (_67249 : real -> Prop) : True = ((term286 _67249) = (term307 _67249)).
Proof. exact (SYM (@lem5151562 _67249)). Qed.
Lemma lem5151564 (_67249 : real -> Prop) : (term286 _67249) = (term307 _67249).
Proof. exact (EQ_MP (@lem5151563 _67249) (@lem0)). Qed.
Lemma lem5151565 (_67249 : real -> Prop) (h1 : term17) : term307 _67249.
Proof. exact (EQ_MP (@lem5151564 _67249) (@lem5151294 _67249 h1)). Qed.
Lemma lem5151567 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5151568 (_67249 : real -> Prop) : (term307 _67249) = (term314 _67249).
Proof. exact (@lem5151567 (term308 _67249) (_67249 = (@EMPTY real))). Qed.
Lemma lem5151570 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5151571 (_67249 : real -> Prop) : (term317 _67249) = (term318 _67249).
Proof. exact (@lem5151570 (term287 _67249) (term243 _67249)). Qed.
Lemma lem5151573 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5151574 (_67249 : real -> Prop) : (term319 _67249) = (@FINITE real _67249).
Proof. exact (@lem5151573 (@FINITE real _67249)). Qed.
Lemma lem5151575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5151576 (_67249 : real -> Prop) : (term320 _67249) = (term321 _67249).
Proof. exact (MK_COMB (@lem5151575) (@lem5151574 _67249)). Qed.
Lemma lem5151577 (_67249 : real -> Prop) : (term304 _67249) = (term304 _67249).
Proof. exact (eq_refl (term304 _67249)). Qed.
Lemma lem5151578 (_67249 : real -> Prop) : (term318 _67249) = (term322 _67249).
Proof. exact (MK_COMB (@lem5151576 _67249) (@lem5151577 _67249)). Qed.
Lemma lem5151579 (_67249 : real -> Prop) : (term317 _67249) = (term322 _67249).
Proof. exact (TRANS (@lem5151571 _67249) (@lem5151578 _67249)). Qed.
Lemma lem5151580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5151581 (_67249 : real -> Prop) : (term323 _67249) = (term324 _67249).
Proof. exact (MK_COMB (@lem5151580) (@lem5151579 _67249)). Qed.
Lemma lem5151582 (_67249 : real -> Prop) : (_67249 = (@EMPTY real)) = (_67249 = (@EMPTY real)).
Proof. exact (eq_refl (_67249 = (@EMPTY real))). Qed.
Lemma lem5151583 (_67249 : real -> Prop) : (term314 _67249) = (term325 _67249).
Proof. exact (MK_COMB (@lem5151581 _67249) (@lem5151582 _67249)). Qed.
Lemma lem5151584 (_67249 : real -> Prop) : (term307 _67249) = (term325 _67249).
Proof. exact (TRANS (@lem5151568 _67249) (@lem5151583 _67249)). Qed.
Lemma lem5151586 (x : real) (s : real -> Prop) (a : real) (h1 : term199 s a x) (h2 : term62 s a) : term322 s.
Proof. exact (conj (@lem5151448 s a x h1) (@lem5151478 s a h2)). Qed.
Lemma lem5151588 (_67249 : real -> Prop) (h1 : term17) : term325 _67249.
Proof. exact (EQ_MP (@lem5151584 _67249) (@lem5151565 _67249 h1)). Qed.
Lemma lem5151589 (s : real -> Prop) (h1 : term17) : term325 s.
Proof. exact (@lem5151588 s h1). Qed.
Lemma lem5151592 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (@lem5151589 s h1 (@lem5151586 x s a h2 h3)). Qed.
Lemma lem5151593 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : term326 s.
Proof. exact (fun h0 : term225 s => @lem5151592 x s a h1 h2 h3). Qed.
Lemma lem5151595 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151596 (s : real -> Prop) : (term326 s) = (s = (@EMPTY real)).
Proof. exact (@lem5151595 (s = (@EMPTY real))). Qed.
Lemma lem5151597 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5151596 s) (@lem5151593 x s a h1 h2 h3)). Qed.
Lemma lem5151600 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5151602 (s : real -> Prop) : (term225 s) = (term327 s).
Proof. exact (@lem5151600 (s = (@EMPTY real))). Qed.
Lemma lem5151605 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term327 s.
Proof. exact (EQ_MP (@lem5151602 s) (@lem5151274 s a x h1)). Qed.
Lemma lem5151608 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : False.
Proof. exact (@lem5151605 s a x h2 (@lem5151597 x s a h1 h2 h3)). Qed.
Lemma lem5151609 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : term328.
Proof. exact (fun h0 : ~ False => @lem5151608 x s a h1 h2 h3). Qed.
Lemma lem5151611 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151612 : term328 = False.
Proof. exact (@lem5151611 False). Qed.
Lemma lem5151613 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : False.
Proof. exact (EQ_MP (@lem5151612) (@lem5151609 x s a h1 h2 h3)). Qed.
Lemma lem5151696 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : real_lt a x.
Proof. exact (proj2 (@lem5150957 s a x h1)). Qed.
Lemma lem5151697 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term329 a x.
Proof. exact (fun h0 : term289 a x => @lem5151696 s a x h1). Qed.
Lemma lem5151699 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151700 (a : real) (x : real) : (term329 a x) = (real_lt a x).
Proof. exact (@lem5151699 (real_lt a x)). Qed.
Lemma lem5151701 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : real_lt a x.
Proof. exact (EQ_MP (@lem5151700 a x) (@lem5151697 s a x h1)). Qed.
Lemma lem5151703 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (proj1 (@lem5150950 s a x h1)). Qed.
Lemma lem5151704 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term292 s.
Proof. exact (fun h0 : term287 s => @lem5151703 s a x h1). Qed.
Lemma lem5151706 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151707 (s : real -> Prop) : (term292 s) = (@FINITE real s).
Proof. exact (@lem5151706 (@FINITE real s)). Qed.
Lemma lem5151708 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (EQ_MP (@lem5151707 s) (@lem5151704 s a x h1)). Qed.
Lemma lem5151710 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term225 s.
Proof. exact (proj2 (@lem5150950 s a x h1)). Qed.
Lemma lem5151711 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term330 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5151710 s a x h1). Qed.
Lemma lem5151713 (p : Prop) : (term306 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5151714 (s : real -> Prop) : (term330 s) = (term225 s).
Proof. exact (@lem5151713 (s = (@EMPTY real))). Qed.
Lemma lem5151715 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term225 s.
Proof. exact (EQ_MP (@lem5151714 s) (@lem5151711 s a x h1)). Qed.
Lemma lem5151717 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : @IN real x s.
Proof. exact (proj1 (@lem5150957 s a x h1)). Qed.
Lemma lem5151718 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term331 x s.
Proof. exact (fun h0 : term297 x s => @lem5151717 s a x h1). Qed.
Lemma lem5151720 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151721 (x : real) (s : real -> Prop) : (term331 x s) = (@IN real x s).
Proof. exact (@lem5151720 (@IN real x s)). Qed.
Lemma lem5151722 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : @IN real x s.
Proof. exact (EQ_MP (@lem5151721 x s) (@lem5151718 s a x h1)). Qed.
Lemma lem5151728 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151729 (_67256 : real) (_67255 : real -> Prop) : (term291 _67256 _67255) = (term332 _67256 _67255).
Proof. exact (@lem5151728 (_67255 = (@EMPTY real)) (term287 _67255) (term226 _67256 _67255)). Qed.
Lemma lem5151755 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5151756 (_67256 : real) (_67255 : real -> Prop) : (term226 _67256 _67255) = (term333 _67256 _67255).
Proof. exact (@lem5151755 (term227 _67256 _67255) (term297 _67256 _67255)). Qed.
Lemma lem5151762 (_67255 : real -> Prop) : (term221 _67255) = (term221 _67255).
Proof. exact (eq_refl (term221 _67255)). Qed.
Lemma lem5151763 (_67256 : real) (_67255 : real -> Prop) : (term334 _67256 _67255) = (term335 _67256 _67255).
Proof. exact (MK_COMB (@lem5151762 _67255) (@lem5151756 _67256 _67255)). Qed.
Lemma lem5151767 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151768 (_67256 : real) (_67255 : real -> Prop) : (term335 _67256 _67255) = (term336 _67256 _67255).
Proof. exact (@lem5151767 (term227 _67256 _67255) (term287 _67255) (term297 _67256 _67255)). Qed.
Lemma lem5151784 (_67256 : real) (_67255 : real -> Prop) : (term334 _67256 _67255) = (term336 _67256 _67255).
Proof. exact (TRANS (@lem5151763 _67256 _67255) (@lem5151768 _67256 _67255)). Qed.
Lemma lem5151785 (_67255 : real -> Prop) : (term310 _67255) = (term310 _67255).
Proof. exact (eq_refl (term310 _67255)). Qed.
Lemma lem5151786 (_67256 : real) (_67255 : real -> Prop) : (term332 _67256 _67255) = (term337 _67256 _67255).
Proof. exact (MK_COMB (@lem5151785 _67255) (@lem5151784 _67256 _67255)). Qed.
Lemma lem5151797 (_67256 : real) (_67255 : real -> Prop) : (term291 _67256 _67255) = (term337 _67256 _67255).
Proof. exact (TRANS (@lem5151729 _67256 _67255) (@lem5151786 _67256 _67255)). Qed.
Lemma lem5151798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5151799 (_67256 : real) (_67255 : real -> Prop) : (term338 _67256 _67255) = (term339 _67256 _67255).
Proof. exact (MK_COMB (@lem5151798) (@lem5151797 _67256 _67255)). Qed.
Lemma lem5151813 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151814 (_67256 : real) (_67255 : real -> Prop) : (term340 _67256 _67255) = (term341 _67256 _67255).
Proof. exact (@lem5151813 (_67255 = (@EMPTY real)) (term287 _67255) (term297 _67256 _67255)). Qed.
Lemma lem5151832 (_67256 : real) (_67255 : real -> Prop) : (term342 _67256 _67255) = (term342 _67256 _67255).
Proof. exact (eq_refl (term342 _67256 _67255)). Qed.
Lemma lem5151833 (_67256 : real) (_67255 : real -> Prop) : (term343 _67256 _67255) = (term344 _67256 _67255).
Proof. exact (MK_COMB (@lem5151832 _67256 _67255) (@lem5151814 _67256 _67255)). Qed.
Lemma lem5151837 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151838 (_67256 : real) (_67255 : real -> Prop) : (term344 _67256 _67255) = (term337 _67256 _67255).
Proof. exact (@lem5151837 (_67255 = (@EMPTY real)) (term227 _67256 _67255) (term345 _67256 _67255)). Qed.
Lemma lem5151866 (_67256 : real) (_67255 : real -> Prop) : (term343 _67256 _67255) = (term337 _67256 _67255).
Proof. exact (TRANS (@lem5151833 _67256 _67255) (@lem5151838 _67256 _67255)). Qed.
Lemma lem5151867 (_67256 : real) (_67255 : real -> Prop) : ((term291 _67256 _67255) = (term343 _67256 _67255)) = ((term337 _67256 _67255) = (term337 _67256 _67255)).
Proof. exact (MK_COMB (@lem5151799 _67256 _67255) (@lem5151866 _67256 _67255)). Qed.
Lemma lem5151869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5151870 (x : Prop) : (x = x) = True.
Proof. exact (@lem5151869 Prop x). Qed.
Lemma lem5151871 (_67256 : real) (_67255 : real -> Prop) : ((term337 _67256 _67255) = (term337 _67256 _67255)) = True.
Proof. exact (@lem5151870 (term337 _67256 _67255)). Qed.
Lemma lem5151872 (_67256 : real) (_67255 : real -> Prop) : ((term291 _67256 _67255) = (term343 _67256 _67255)) = True.
Proof. exact (TRANS (@lem5151867 _67256 _67255) (@lem5151871 _67256 _67255)). Qed.
Lemma lem5151873 (_67256 : real) (_67255 : real -> Prop) : True = ((term291 _67256 _67255) = (term343 _67256 _67255)).
Proof. exact (SYM (@lem5151872 _67256 _67255)). Qed.
Lemma lem5151874 (_67256 : real) (_67255 : real -> Prop) : (term291 _67256 _67255) = (term343 _67256 _67255).
Proof. exact (EQ_MP (@lem5151873 _67256 _67255) (@lem0)). Qed.
Lemma lem5151875 (_67256 : real) (_67255 : real -> Prop) (h1 : term17) : term343 _67256 _67255.
Proof. exact (EQ_MP (@lem5151874 _67256 _67255) (@lem5151360 _67256 _67255 h1)). Qed.
Lemma lem5151877 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5151878 (_67256 : real) (_67255 : real -> Prop) : (term343 _67256 _67255) = (term346 _67256 _67255).
Proof. exact (@lem5151877 (term340 _67256 _67255) (term227 _67256 _67255)). Qed.
Lemma lem5151880 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5151881 (_67256 : real) (_67255 : real -> Prop) : (term347 _67256 _67255) = (term348 _67256 _67255).
Proof. exact (@lem5151880 (term287 _67255) (term349 _67256 _67255)). Qed.
Lemma lem5151883 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5151884 (_67255 : real -> Prop) : (term319 _67255) = (@FINITE real _67255).
Proof. exact (@lem5151883 (@FINITE real _67255)). Qed.
Lemma lem5151885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5151886 (_67255 : real -> Prop) : (term320 _67255) = (term321 _67255).
Proof. exact (MK_COMB (@lem5151885) (@lem5151884 _67255)). Qed.
Lemma lem5151888 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5151889 (_67256 : real) (_67255 : real -> Prop) : (term350 _67256 _67255) = (term351 _67256 _67255).
Proof. exact (@lem5151888 (_67255 = (@EMPTY real)) (term297 _67256 _67255)). Qed.
Lemma lem5151891 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5151892 (_67256 : real) (_67255 : real -> Prop) : (term352 _67256 _67255) = (@IN real _67256 _67255).
Proof. exact (@lem5151891 (@IN real _67256 _67255)). Qed.
Lemma lem5151893 (_67255 : real -> Prop) : (term353 _67255) = (term353 _67255).
Proof. exact (eq_refl (term353 _67255)). Qed.
Lemma lem5151894 (_67256 : real) (_67255 : real -> Prop) : (term351 _67256 _67255) = (term354 _67256 _67255).
Proof. exact (MK_COMB (@lem5151893 _67255) (@lem5151892 _67256 _67255)). Qed.
Lemma lem5151895 (_67256 : real) (_67255 : real -> Prop) : (term350 _67256 _67255) = (term354 _67256 _67255).
Proof. exact (TRANS (@lem5151889 _67256 _67255) (@lem5151894 _67256 _67255)). Qed.
Lemma lem5151896 (_67256 : real) (_67255 : real -> Prop) : (term348 _67256 _67255) = (term355 _67256 _67255).
Proof. exact (MK_COMB (@lem5151886 _67255) (@lem5151895 _67256 _67255)). Qed.
Lemma lem5151897 (_67256 : real) (_67255 : real -> Prop) : (term347 _67256 _67255) = (term355 _67256 _67255).
Proof. exact (TRANS (@lem5151881 _67256 _67255) (@lem5151896 _67256 _67255)). Qed.
Lemma lem5151898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5151899 (_67256 : real) (_67255 : real -> Prop) : (term356 _67256 _67255) = (term357 _67256 _67255).
Proof. exact (MK_COMB (@lem5151898) (@lem5151897 _67256 _67255)). Qed.
Lemma lem5151900 (_67256 : real) (_67255 : real -> Prop) : (term227 _67256 _67255) = (term227 _67256 _67255).
Proof. exact (eq_refl (term227 _67256 _67255)). Qed.
Lemma lem5151901 (_67256 : real) (_67255 : real -> Prop) : (term346 _67256 _67255) = (term358 _67256 _67255).
Proof. exact (MK_COMB (@lem5151899 _67256 _67255) (@lem5151900 _67256 _67255)). Qed.
Lemma lem5151902 (_67256 : real) (_67255 : real -> Prop) : (term343 _67256 _67255) = (term358 _67256 _67255).
Proof. exact (TRANS (@lem5151878 _67256 _67255) (@lem5151901 _67256 _67255)). Qed.
Lemma lem5151904 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) (h2 : term199 s a x) : term354 x s.
Proof. exact (conj (@lem5151715 s a x h2) (@lem5151722 s a x h1)). Qed.
Lemma lem5151905 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) (h2 : term199 s a x) : term355 x s.
Proof. exact (conj (@lem5151708 s a x h2) (@lem5151904 s a x h1 h2)). Qed.
Lemma lem5151907 (_67256 : real) (_67255 : real -> Prop) (h1 : term17) : term358 _67256 _67255.
Proof. exact (EQ_MP (@lem5151902 _67256 _67255) (@lem5151875 _67256 _67255 h1)). Qed.
Lemma lem5151908 (x : real) (s : real -> Prop) (h1 : term17) : term358 x s.
Proof. exact (@lem5151907 x s h1). Qed.
Lemma lem5151911 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term227 x s.
Proof. exact (@lem5151908 x s h1 (@lem5151905 s a x h2 h3)). Qed.
Lemma lem5151912 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term359 x s.
Proof. exact (fun h0 : term360 x s => @lem5151911 s a x h1 h2 h3). Qed.
Lemma lem5151914 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5151915 (x : real) (s : real -> Prop) : (term359 x s) = (term227 x s).
Proof. exact (@lem5151914 (term227 x s)). Qed.
Lemma lem5151916 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term227 x s.
Proof. exact (EQ_MP (@lem5151915 x s) (@lem5151912 s a x h1 h2 h3)). Qed.
Lemma lem5151922 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151923 (_67253 : real) (_67252 : real) (_67254 : real) : (term288 _67253 _67252 _67254) = (term361 _67253 _67252 _67254).
Proof. exact (@lem5151922 (term290 _67253 _67254) (term289 _67252 _67253) (real_lt _67252 _67254)). Qed.
Lemma lem5151937 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5151938 (_67254 : real) (_67252 : real) (_67253 : real) : (term362 _67253 _67252 _67254) = (term363 _67254 _67252 _67253).
Proof. exact (@lem5151937 (real_lt _67252 _67254) (term289 _67252 _67253)). Qed.
Lemma lem5151944 (_67253 : real) (_67254 : real) : (term364 _67253 _67254) = (term364 _67253 _67254).
Proof. exact (eq_refl (term364 _67253 _67254)). Qed.
Lemma lem5151945 (_67254 : real) (_67252 : real) (_67253 : real) : (term361 _67253 _67252 _67254) = (term365 _67254 _67252 _67253).
Proof. exact (MK_COMB (@lem5151944 _67253 _67254) (@lem5151938 _67254 _67252 _67253)). Qed.
Lemma lem5151949 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5151950 (_67254 : real) (_67252 : real) (_67253 : real) : (term365 _67254 _67252 _67253) = (term366 _67254 _67252 _67253).
Proof. exact (@lem5151949 (real_lt _67252 _67254) (term290 _67253 _67254) (term289 _67252 _67253)). Qed.
Lemma lem5151966 (_67254 : real) (_67252 : real) (_67253 : real) : (term361 _67253 _67252 _67254) = (term366 _67254 _67252 _67253).
Proof. exact (TRANS (@lem5151945 _67254 _67252 _67253) (@lem5151950 _67254 _67252 _67253)). Qed.
Lemma lem5151967 (_67254 : real) (_67252 : real) (_67253 : real) : (term288 _67253 _67252 _67254) = (term366 _67254 _67252 _67253).
Proof. exact (TRANS (@lem5151923 _67253 _67252 _67254) (@lem5151966 _67254 _67252 _67253)). Qed.
Lemma lem5151968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5151969 (_67254 : real) (_67252 : real) (_67253 : real) : (term367 _67253 _67252 _67254) = (term368 _67254 _67252 _67253).
Proof. exact (MK_COMB (@lem5151968) (@lem5151967 _67254 _67252 _67253)). Qed.
Lemma lem5151983 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5151984 (_67254 : real) (_67252 : real) (_67253 : real) : (term208 _67252 _67253 _67254) = (term369 _67254 _67252 _67253).
Proof. exact (@lem5151983 (term290 _67253 _67254) (term289 _67252 _67253)). Qed.
Lemma lem5151990 (_67252 : real) (_67254 : real) : (term370 _67252 _67254) = (term370 _67252 _67254).
Proof. exact (eq_refl (term370 _67252 _67254)). Qed.
Lemma lem5151991 (_67254 : real) (_67252 : real) (_67253 : real) : (term371 _67252 _67253 _67254) = (term366 _67254 _67252 _67253).
Proof. exact (MK_COMB (@lem5151990 _67252 _67254) (@lem5151984 _67254 _67252 _67253)). Qed.
Lemma lem5152002 (_67254 : real) (_67252 : real) (_67253 : real) : ((term288 _67253 _67252 _67254) = (term371 _67252 _67253 _67254)) = ((term366 _67254 _67252 _67253) = (term366 _67254 _67252 _67253)).
Proof. exact (MK_COMB (@lem5151969 _67254 _67252 _67253) (@lem5151991 _67254 _67252 _67253)). Qed.
Lemma lem5152004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5152005 (x : Prop) : (x = x) = True.
Proof. exact (@lem5152004 Prop x). Qed.
Lemma lem5152006 (_67254 : real) (_67252 : real) (_67253 : real) : ((term366 _67254 _67252 _67253) = (term366 _67254 _67252 _67253)) = True.
Proof. exact (@lem5152005 (term366 _67254 _67252 _67253)). Qed.
Lemma lem5152007 (_67252 : real) (_67253 : real) (_67254 : real) : ((term288 _67253 _67252 _67254) = (term371 _67252 _67253 _67254)) = True.
Proof. exact (TRANS (@lem5152002 _67254 _67252 _67253) (@lem5152006 _67254 _67252 _67253)). Qed.
Lemma lem5152008 (_67252 : real) (_67253 : real) (_67254 : real) : True = ((term288 _67253 _67252 _67254) = (term371 _67252 _67253 _67254)).
Proof. exact (SYM (@lem5152007 _67252 _67253 _67254)). Qed.
Lemma lem5152009 (_67252 : real) (_67253 : real) (_67254 : real) : (term288 _67253 _67252 _67254) = (term371 _67252 _67253 _67254).
Proof. exact (EQ_MP (@lem5152008 _67252 _67253 _67254) (@lem0)). Qed.
Lemma lem5152010 (_67252 : real) (_67253 : real) (_67254 : real) (h1 : term37) : term371 _67252 _67253 _67254.
Proof. exact (EQ_MP (@lem5152009 _67252 _67253 _67254) (@lem5151322 _67253 _67252 _67254 h1)). Qed.
Lemma lem5152012 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5152013 (_67253 : real) (_67252 : real) (_67254 : real) : (term371 _67252 _67253 _67254) = (term372 _67253 _67252 _67254).
Proof. exact (@lem5152012 (term208 _67252 _67253 _67254) (real_lt _67252 _67254)). Qed.
Lemma lem5152015 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5152016 (_67252 : real) (_67253 : real) (_67254 : real) : (term373 _67252 _67253 _67254) = (term374 _67252 _67253 _67254).
Proof. exact (@lem5152015 (term289 _67252 _67253) (term290 _67253 _67254)). Qed.
Lemma lem5152018 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5152019 (_67252 : real) (_67253 : real) : (term299 _67252 _67253) = (real_lt _67252 _67253).
Proof. exact (@lem5152018 (real_lt _67252 _67253)). Qed.
Lemma lem5152020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5152021 (_67252 : real) (_67253 : real) : (term375 _67252 _67253) = (term376 _67252 _67253).
Proof. exact (MK_COMB (@lem5152020) (@lem5152019 _67252 _67253)). Qed.
Lemma lem5152023 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5152024 (_67253 : real) (_67254 : real) : (term377 _67253 _67254) = (real_le _67253 _67254).
Proof. exact (@lem5152023 (real_le _67253 _67254)). Qed.
Lemma lem5152025 (_67252 : real) (_67253 : real) (_67254 : real) : (term374 _67252 _67253 _67254) = (term213 _67252 _67253 _67254).
Proof. exact (MK_COMB (@lem5152021 _67252 _67253) (@lem5152024 _67253 _67254)). Qed.
Lemma lem5152026 (_67252 : real) (_67253 : real) (_67254 : real) : (term373 _67252 _67253 _67254) = (term213 _67252 _67253 _67254).
Proof. exact (TRANS (@lem5152016 _67252 _67253 _67254) (@lem5152025 _67252 _67253 _67254)). Qed.
Lemma lem5152027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5152028 (_67252 : real) (_67253 : real) (_67254 : real) : (term378 _67252 _67253 _67254) = (term379 _67252 _67253 _67254).
Proof. exact (MK_COMB (@lem5152027) (@lem5152026 _67252 _67253 _67254)). Qed.
Lemma lem5152029 (_67252 : real) (_67254 : real) : (real_lt _67252 _67254) = (real_lt _67252 _67254).
Proof. exact (eq_refl (real_lt _67252 _67254)). Qed.
Lemma lem5152030 (_67253 : real) (_67252 : real) (_67254 : real) : (term372 _67253 _67252 _67254) = (term31 _67253 _67252 _67254).
Proof. exact (MK_COMB (@lem5152028 _67252 _67253 _67254) (@lem5152029 _67252 _67254)). Qed.
Lemma lem5152031 (_67253 : real) (_67252 : real) (_67254 : real) : (term371 _67252 _67253 _67254) = (term31 _67253 _67252 _67254).
Proof. exact (TRANS (@lem5152013 _67253 _67252 _67254) (@lem5152030 _67253 _67252 _67254)). Qed.
Lemma lem5152033 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term380 a x s.
Proof. exact (conj (@lem5151701 s a x h2) (@lem5151916 s a x h1 h2 h3)). Qed.
Lemma lem5152035 (_67253 : real) (_67252 : real) (_67254 : real) (h1 : term37) : term31 _67253 _67252 _67254.
Proof. exact (EQ_MP (@lem5152031 _67253 _67252 _67254) (@lem5152010 _67252 _67253 _67254 h1)). Qed.
Lemma lem5152036 (x : real) (a : real) (s : real -> Prop) (h1 : term37) : term381 x a s.
Proof. exact (@lem5152035 x a (sup s) h1). Qed.
Lemma lem5152039 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term42 a s.
Proof. exact (@lem5152036 x a s h2 (@lem5152033 s a x h1 h3 h4)). Qed.
Lemma lem5152040 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term294 a s.
Proof. exact (fun h0 : term135 a s => @lem5152039 s a x h1 h2 h3 h4). Qed.
Lemma lem5152042 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5152043 (a : real) (s : real -> Prop) : (term294 a s) = (term42 a s).
Proof. exact (@lem5152042 (term42 a s)). Qed.
Lemma lem5152044 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term42 a s.
Proof. exact (EQ_MP (@lem5152043 a s) (@lem5152040 s a x h1 h2 h3 h4)). Qed.
Lemma lem5152047 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5152049 (a : real) (s : real -> Prop) : (term135 a s) = (term382 a s).
Proof. exact (@lem5152047 (term42 a s)). Qed.
Lemma lem5152052 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term382 a s.
Proof. exact (EQ_MP (@lem5152049 a s) (@lem5151328 s a x h1)). Qed.
Lemma lem5152055 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : False.
Proof. exact (@lem5152052 s a x h3 (@lem5152044 s a x h1 h2 h3 h4)). Qed.
Lemma lem5152056 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term328.
Proof. exact (fun h0 : ~ False => @lem5152055 s a x h1 h2 h3 h4). Qed.
Lemma lem5152058 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5152059 : term328 = False.
Proof. exact (@lem5152058 False). Qed.
Lemma lem5152060 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : False.
Proof. exact (EQ_MP (@lem5152059) (@lem5152056 s a x h1 h2 h3 h4)). Qed.
Lemma lem5152061 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term199 s a x) : False.
Proof. exact (or_elim (@lem5150949 s a x h3) (fun h0 : term62 s a => @lem5151613 x s a h1 h3 h0) (fun h0 : term141 s a x => @lem5152060 s a x h1 h2 h0 h3)). Qed.
Lemma lem5152062 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term199 s a x) : (term199 s a x) = False.
Proof. exact (prop_ext (fun h4 : term199 s a x => @lem5152061 s a x h1 h2 h3) (fun h4 : False => @lem5150948 s a x h3)). Qed.
Lemma lem5152063 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term199 s a x) : False.
Proof. exact (EQ_MP (@lem5152062 s a x h1 h2 h3) (@lem5150948 s a x h3)). Qed.
Lemma lem5152064 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term202 s a) : False.
Proof. exact (ex_elim (@lem5150787 s a h3) (fun x : real => fun h0 : term201 s a x => @lem5152063 s a x h1 h2 h0)). Qed.
Lemma lem5152065 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term204 s) : False.
Proof. exact (ex_elim (@lem5150786 s h3) (fun a : real => fun h0 : term203 s a => @lem5152064 s a h1 h2 h0)). Qed.
Lemma lem5152066 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5150570 h3) (fun s : real -> Prop => fun h0 : term205 s => @lem5152065 s h1 h2 h0)). Qed.
Lemma lem5152067 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5152066 h0 h1 h2). Qed.
Lemma lem5152068 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5152069 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5152068) (@lem5152067 h1 h2)). Qed.
Lemma lem5152070 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5152069 h0 h1). Qed.
Lemma lem5152071 : term22.
Proof. exact (fun h0 : term10 => @lem5152070 h0). Qed.
Lemma lem5152072 : term11.
Proof. exact (EQ_MP (@lem5150072) (@lem5152071)). Qed.
Lemma lem5152074 : term11.
Proof. exact (@lem5149804 (@lem5152072)). Qed.
Lemma lem5152075 (h1 : term10) : term19.
Proof. exact (@lem5152074 (@lem5149789 h1)). Qed.
Lemma lem5152076 (h1 : term10) : term15.
Proof. exact (@lem5152075 h1 (@lem1370312)). Qed.
Lemma lem5152077 (h1 : term10) : False.
Proof. exact (@lem5152076 h1 (@lem5145274)). Qed.
Lemma lem5152078 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5152077 h1) (fun h2 : False => @lem5149789 h1)). Qed.
Lemma lem5152079 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5152078 h1) (@lem5149789 h1)). Qed.
Lemma lem5152080 : term9.
Proof. exact (fun h0 : term10 => @lem5152079 h0). Qed.
Lemma lem5152081 : term8.
Proof. exact (EQ_MP (@lem5149788) (@lem5152080)). Qed.
