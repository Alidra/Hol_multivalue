Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INF_LE_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
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
Lemma lem5224799 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5224800 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5224801 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5224800 t1) (@lem5224799 t1)). Qed.
Lemma lem5224802 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5224801 t1 t2). Qed.
Lemma lem5224803 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5224804 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5224803 t1 t2) (@lem5224802 t1 t2)). Qed.
Lemma lem5224805 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5224804 t1 t2 t3). Qed.
Lemma lem5224806 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5224807 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5224806 t1 t2 t3) (@lem5224805 t1 t2 t3)). Qed.
Lemma lem5224808 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5224807 t1 t2 t3)). Qed.
Lemma lem5224810 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5224811 : term8 = term9.
Proof. exact (@lem5224810 term8). Qed.
Lemma lem5224812 : term9 = term8.
Proof. exact (SYM (@lem5224811)). Qed.
Lemma lem5224813 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5224816 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5224817 : term12.
Proof. exact (fun h0 : term11 => @lem5224816 h0). Qed.
Lemma lem5224818 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5224819 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5224820 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5224818 h2 (@lem5224819 h1)). Qed.
Lemma lem5224821 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5224820 h1 h0). Qed.
Lemma lem5224822 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5224823 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5224821 h1 (@lem5224822 h2)). Qed.
Lemma lem5224824 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5224823 h0 h1). Qed.
Lemma lem5224825 : term14.
Proof. exact (fun h0 : term12 => @lem5224824 h0). Qed.
Lemma lem5224828 : term12.
Proof. exact (@lem5224825 (@lem5224817)). Qed.
Lemma lem5224912 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5224913 : term15 = term16.
Proof. exact (@lem5224912 term17). Qed.
Lemma lem5224930 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5224931 : term19 = term20.
Proof. exact (MK_COMB (@lem5224930) (@lem5224913)). Qed.
Lemma lem5224934 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5224941 : term11 = term22.
Proof. exact (MK_COMB (@lem5224934) (@lem5224931)). Qed.
Lemma lem5224946 (s : real -> Prop) (x : real) : (term23 s x) = (term23 s x).
Proof. exact (eq_refl (term23 s x)). Qed.
Lemma lem5224947 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5224946 s x)). Qed.
Lemma lem5224948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5224949 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5224948) (@lem5224947 s)). Qed.
Lemma lem5224952 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5224953 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5224952 s) (@lem5224949 s)). Qed.
Lemma lem5224962 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5224963 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5224962 s) (@lem5224953 s)). Qed.
Lemma lem5224964 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5224963 s)). Qed.
Lemma lem5224965 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5224966 : term17 = term17.
Proof. exact (MK_COMB (@lem5224965) (@lem5224964)). Qed.
Lemma lem5224967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5224968 : term16 = term16.
Proof. exact (MK_COMB (@lem5224967) (@lem5224966)). Qed.
Lemma lem5224977 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5224978 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5224977 y x z)). Qed.
Lemma lem5224979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5224980 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5224979) (@lem5224978 y x)). Qed.
Lemma lem5224981 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5224980 y x)). Qed.
Lemma lem5224982 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5224983 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5224982) (@lem5224981 x)). Qed.
Lemma lem5224984 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5224983 x)). Qed.
Lemma lem5224985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5224986 : term37 = term37.
Proof. exact (MK_COMB (@lem5224985) (@lem5224984)). Qed.
Lemma lem5224987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5224988 : term18 = term18.
Proof. exact (MK_COMB (@lem5224987) (@lem5224986)). Qed.
Lemma lem5224989 : term20 = term20.
Proof. exact (MK_COMB (@lem5224988) (@lem5224968)). Qed.
Lemma lem5224994 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term38 s x a).
Proof. exact (eq_refl (term38 s x a)). Qed.
Lemma lem5224995 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5224994 s x a)). Qed.
Lemma lem5224996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5224997 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5224996) (@lem5224995 s a)). Qed.
Lemma lem5225000 (s : real -> Prop) (a : real) : (term41 s a) = (term41 s a).
Proof. exact (eq_refl (term41 s a)). Qed.
Lemma lem5225001 (s : real -> Prop) (a : real) : ((term42 s a) = (term40 s a)) = ((term42 s a) = (term40 s a)).
Proof. exact (MK_COMB (@lem5225000 s a) (@lem5224997 s a)). Qed.
Lemma lem5225010 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5225011 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5225010 s) (@lem5225001 s a)). Qed.
Lemma lem5225012 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5225011 s a)). Qed.
Lemma lem5225013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225014 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5225013) (@lem5225012 s)). Qed.
Lemma lem5225015 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5225014 s)). Qed.
Lemma lem5225016 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5225017 : term8 = term8.
Proof. exact (MK_COMB (@lem5225016) (@lem5225015)). Qed.
Lemma lem5225018 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5225019 : term10 = term10.
Proof. exact (MK_COMB (@lem5225018) (@lem5225017)). Qed.
Lemma lem5225020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5225021 : term21 = term21.
Proof. exact (MK_COMB (@lem5225020) (@lem5225019)). Qed.
Lemma lem5225022 : term22 = term22.
Proof. exact (MK_COMB (@lem5225021) (@lem5224989)). Qed.
Lemma lem5225095 : term11 = term22.
Proof. exact (TRANS (@lem5224941) (@lem5225022)). Qed.
Lemma lem5225096 : term22 = term11.
Proof. exact (SYM (@lem5225095)). Qed.
Lemma lem5225097 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5225098 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5225099 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5225115 (s : real -> Prop) (x : real) (a : real) : (term47 s x a) = (term48 s x a).
Proof. exact (@lem17045 (@IN real x s) (real_le x a)). Qed.
Lemma lem5225118 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term38 s x a).
Proof. exact (eq_refl (term38 s x a)). Qed.
Lemma lem5225119 (P : real -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5225120 (s : real -> Prop) (a : real) : (term51 s a) = (term52 s a).
Proof. exact (@lem5225119 (term39 s a)). Qed.
Lemma lem5225121 (s : real -> Prop) (x : real) (a : real) : (term53 s a x) = (term38 s x a).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5225122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5225123 (s : real -> Prop) (x : real) (a : real) : (term54 s a x) = (term47 s x a).
Proof. exact (MK_COMB (@lem5225122) (@lem5225121 s x a)). Qed.
Lemma lem5225124 (s : real -> Prop) (x : real) (a : real) : (term54 s a x) = (term48 s x a).
Proof. exact (TRANS (@lem5225123 s x a) (@lem5225115 s x a)). Qed.
Lemma lem5225125 (s : real -> Prop) (a : real) : (term55 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5225124 s x a)). Qed.
Lemma lem5225126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225127 (s : real -> Prop) (a : real) : (term52 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5225126) (@lem5225125 s a)). Qed.
Lemma lem5225128 (s : real -> Prop) (a : real) : (term51 s a) = (term57 s a).
Proof. exact (TRANS (@lem5225120 s a) (@lem5225127 s a)). Qed.
Lemma lem5225129 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5225118 s x a)). Qed.
Lemma lem5225130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225131 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5225130) (@lem5225129 s a)). Qed.
Lemma lem5225133 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5225134 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5225133 s a) (@lem5225131 s a)). Qed.
Lemma lem5225136 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (eq_refl (term60 s a)). Qed.
Lemma lem5225137 (s : real -> Prop) (a : real) : (term61 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5225136 s a) (@lem5225128 s a)). Qed.
Lemma lem5225138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225139 (s : real -> Prop) (a : real) : (term63 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5225138) (@lem5225137 s a)). Qed.
Lemma lem5225140 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5225139 s a) (@lem5225134 s a)). Qed.
Lemma lem5225141 (s : real -> Prop) (a : real) : (term67 s a) = (term65 s a).
Proof. exact (@lem17646 (term42 s a) (term40 s a)). Qed.
Lemma lem5225142 (s : real -> Prop) (a : real) : (term67 s a) = (term66 s a).
Proof. exact (TRANS (@lem5225141 s a) (@lem5225140 s a)). Qed.
Lemma lem5225144 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225145 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5225144 s) (@lem5225142 s a)). Qed.
Lemma lem5225146 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17362 (term72 s) ((term42 s a) = (term40 s a))). Qed.
Lemma lem5225147 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5225146 s a) (@lem5225145 s a)). Qed.
Lemma lem5225148 (P : real -> Prop) : (term73 P) = (term74 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5225149 (s : real -> Prop) : (term75 s) = (term76 s).
Proof. exact (@lem5225148 (term44 s)). Qed.
Lemma lem5225150 (s : real -> Prop) (a : real) : (term77 s a) = (term43 s a).
Proof. exact (eq_refl (term77 s a)). Qed.
Lemma lem5225151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5225152 (s : real -> Prop) (a : real) : (term78 s a) = (term71 s a).
Proof. exact (MK_COMB (@lem5225151) (@lem5225150 s a)). Qed.
Lemma lem5225153 (s : real -> Prop) (a : real) : (term78 s a) = (term70 s a).
Proof. exact (TRANS (@lem5225152 s a) (@lem5225147 s a)). Qed.
Lemma lem5225154 (s : real -> Prop) : (term79 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5225153 s a)). Qed.
Lemma lem5225155 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225156 (s : real -> Prop) : (term76 s) = (term81 s).
Proof. exact (MK_COMB (@lem5225155) (@lem5225154 s)). Qed.
Lemma lem5225157 (s : real -> Prop) : (term75 s) = (term81 s).
Proof. exact (TRANS (@lem5225149 s) (@lem5225156 s)). Qed.
Lemma lem5225158 (P : type1022) : (term82 P) = (term83 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5225159 : term10 = term84.
Proof. exact (@lem5225158 term46). Qed.
Lemma lem5225160 (s : real -> Prop) : (term85 s) = (term45 s).
Proof. exact (eq_refl (term85 s)). Qed.
Lemma lem5225161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5225162 (s : real -> Prop) : (term86 s) = (term75 s).
Proof. exact (MK_COMB (@lem5225161) (@lem5225160 s)). Qed.
Lemma lem5225163 (s : real -> Prop) : (term86 s) = (term81 s).
Proof. exact (TRANS (@lem5225162 s) (@lem5225157 s)). Qed.
Lemma lem5225164 : term87 = term88.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5225163 s)). Qed.
Lemma lem5225165 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5225166 : term84 = term89.
Proof. exact (MK_COMB (@lem5225165) (@lem5225164)). Qed.
Lemma lem5225167 : term10 = term89.
Proof. exact (TRANS (@lem5225159) (@lem5225166)). Qed.
Lemma lem5225173 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5225174 (P : Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem5225173 real P Q). Qed.
Lemma lem5225175 (s : real -> Prop) : (term94 s) = (term95 s).
Proof. exact (@lem5225174 (term72 s) (term96 s)). Qed.
Lemma lem5225176 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5225177 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225178 (s : real -> Prop) (a : real) : (term98 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5225177 s) (@lem5225176 s a)). Qed.
Lemma lem5225179 (s : real -> Prop) : (term99 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5225178 s a)). Qed.
Lemma lem5225180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225181 (s : real -> Prop) : (term94 s) = (term81 s).
Proof. exact (MK_COMB (@lem5225180) (@lem5225179 s)). Qed.
Lemma lem5225182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225183 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem5225182) (@lem5225181 s)). Qed.
Lemma lem5225184 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5225185 (s : real -> Prop) : (term102 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5225184 s a)). Qed.
Lemma lem5225186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225187 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5225186) (@lem5225185 s)). Qed.
Lemma lem5225188 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225189 (s : real -> Prop) : (term95 s) = (term105 s).
Proof. exact (MK_COMB (@lem5225188 s) (@lem5225187 s)). Qed.
Lemma lem5225190 (s : real -> Prop) : ((term94 s) = (term95 s)) = ((term81 s) = (term105 s)).
Proof. exact (MK_COMB (@lem5225183 s) (@lem5225189 s)). Qed.
Lemma lem5225191 (s : real -> Prop) : (term81 s) = (term105 s).
Proof. exact (EQ_MP (@lem5225190 s) (@lem5225175 s)). Qed.
Lemma lem5225193 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5225194 (P : real -> Prop) (Q : real -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem5225193 real P Q). Qed.
Lemma lem5225195 (s : real -> Prop) : (term110 s) = (term111 s).
Proof. exact (@lem5225194 (term112 s) (term113 s)). Qed.
Lemma lem5225196 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5225197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225198 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5225197) (@lem5225196 s a)). Qed.
Lemma lem5225199 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5225200 (s : real -> Prop) (a : real) : (term117 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5225198 s a) (@lem5225199 s a)). Qed.
Lemma lem5225201 (s : real -> Prop) : (term118 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5225200 s a)). Qed.
Lemma lem5225202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225203 (s : real -> Prop) : (term110 s) = (term104 s).
Proof. exact (MK_COMB (@lem5225202) (@lem5225201 s)). Qed.
Lemma lem5225204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225205 (s : real -> Prop) : (term119 s) = (term120 s).
Proof. exact (MK_COMB (@lem5225204) (@lem5225203 s)). Qed.
Lemma lem5225206 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5225207 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5225206 s a)). Qed.
Lemma lem5225208 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225209 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5225208) (@lem5225207 s)). Qed.
Lemma lem5225210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225211 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5225210) (@lem5225209 s)). Qed.
Lemma lem5225212 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5225213 (s : real -> Prop) : (term126 s) = (term113 s).
Proof. exact (fun_ext (fun a : real => @lem5225212 s a)). Qed.
Lemma lem5225214 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225215 (s : real -> Prop) : (term127 s) = (term128 s).
Proof. exact (MK_COMB (@lem5225214) (@lem5225213 s)). Qed.
Lemma lem5225216 (s : real -> Prop) : (term111 s) = (term129 s).
Proof. exact (MK_COMB (@lem5225211 s) (@lem5225215 s)). Qed.
Lemma lem5225217 (s : real -> Prop) : ((term110 s) = (term111 s)) = ((term104 s) = (term129 s)).
Proof. exact (MK_COMB (@lem5225205 s) (@lem5225216 s)). Qed.
Lemma lem5225218 (s : real -> Prop) : (term104 s) = (term129 s).
Proof. exact (EQ_MP (@lem5225217 s) (@lem5225195 s)). Qed.
Lemma lem5225411 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225412 (s : real -> Prop) : (term105 s) = (term130 s).
Proof. exact (MK_COMB (@lem5225411 s) (@lem5225218 s)). Qed.
Lemma lem5225413 (s : real -> Prop) : (term81 s) = (term130 s).
Proof. exact (TRANS (@lem5225191 s) (@lem5225412 s)). Qed.
Lemma lem5225414 : term88 = term131.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5225413 s)). Qed.
Lemma lem5225415 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5225416 : term89 = term132.
Proof. exact (MK_COMB (@lem5225415) (@lem5225414)). Qed.
Lemma lem5225466 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5225467 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5225466 real P Q). Qed.
Lemma lem5225468 (s : real -> Prop) (a : real) : (term133 s a) = (term134 s a).
Proof. exact (@lem5225467 (term135 s a) (term39 s a)). Qed.
Lemma lem5225469 (s : real -> Prop) (x : real) (a : real) : (term53 s a x) = (term38 s x a).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5225470 (s : real -> Prop) (a : real) : (term136 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5225469 s x a)). Qed.
Lemma lem5225471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225472 (s : real -> Prop) (a : real) : (term137 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5225471) (@lem5225470 s a)). Qed.
Lemma lem5225473 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5225474 (s : real -> Prop) (a : real) : (term133 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5225473 s a) (@lem5225472 s a)). Qed.
Lemma lem5225475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225476 (s : real -> Prop) (a : real) : (term138 s a) = (term139 s a).
Proof. exact (MK_COMB (@lem5225475) (@lem5225474 s a)). Qed.
Lemma lem5225477 (s : real -> Prop) (x : real) (a : real) : (term53 s a x) = (term38 s x a).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5225478 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5225479 (s : real -> Prop) (x : real) (a : real) : (term140 s a x) = (term141 s x a).
Proof. exact (MK_COMB (@lem5225478 s a) (@lem5225477 s x a)). Qed.
Lemma lem5225480 (s : real -> Prop) (a : real) : (term142 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5225479 s x a)). Qed.
Lemma lem5225481 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225482 (s : real -> Prop) (a : real) : (term134 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5225481) (@lem5225480 s a)). Qed.
Lemma lem5225483 (s : real -> Prop) (a : real) : ((term133 s a) = (term134 s a)) = ((term59 s a) = (term144 s a)).
Proof. exact (MK_COMB (@lem5225476 s a) (@lem5225482 s a)). Qed.
Lemma lem5225484 (s : real -> Prop) (a : real) : (term59 s a) = (term144 s a).
Proof. exact (EQ_MP (@lem5225483 s a) (@lem5225468 s a)). Qed.
Lemma lem5225485 (s : real -> Prop) : (term113 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5225484 s a)). Qed.
Lemma lem5225486 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225487 (s : real -> Prop) : (term128 s) = (term146 s).
Proof. exact (MK_COMB (@lem5225486) (@lem5225485 s)). Qed.
Lemma lem5225488 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (eq_refl (term125 s)). Qed.
Lemma lem5225489 (s : real -> Prop) : (term129 s) = (term147 s).
Proof. exact (MK_COMB (@lem5225488 s) (@lem5225487 s)). Qed.
Lemma lem5225491 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5225492 (P : real -> Prop) (Q : real -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem5225491 real P Q). Qed.
Lemma lem5225493 (s : real -> Prop) : (term148 s) = (term149 s).
Proof. exact (@lem5225492 (term112 s) (term145 s)). Qed.
Lemma lem5225494 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5225495 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5225494 s a)). Qed.
Lemma lem5225496 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225497 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5225496) (@lem5225495 s)). Qed.
Lemma lem5225498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225499 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5225498) (@lem5225497 s)). Qed.
Lemma lem5225500 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5225501 (s : real -> Prop) : (term151 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5225500 s a)). Qed.
Lemma lem5225502 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225503 (s : real -> Prop) : (term152 s) = (term146 s).
Proof. exact (MK_COMB (@lem5225502) (@lem5225501 s)). Qed.
Lemma lem5225504 (s : real -> Prop) : (term148 s) = (term147 s).
Proof. exact (MK_COMB (@lem5225499 s) (@lem5225503 s)). Qed.
Lemma lem5225505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225506 (s : real -> Prop) : (term153 s) = (term154 s).
Proof. exact (MK_COMB (@lem5225505) (@lem5225504 s)). Qed.
Lemma lem5225507 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5225508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225509 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5225508) (@lem5225507 s a)). Qed.
Lemma lem5225510 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5225511 (s : real -> Prop) (a : real) : (term155 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5225509 s a) (@lem5225510 s a)). Qed.
Lemma lem5225512 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (fun_ext (fun a : real => @lem5225511 s a)). Qed.
Lemma lem5225513 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225514 (s : real -> Prop) : (term149 s) = (term159 s).
Proof. exact (MK_COMB (@lem5225513) (@lem5225512 s)). Qed.
Lemma lem5225515 (s : real -> Prop) : ((term148 s) = (term149 s)) = ((term147 s) = (term159 s)).
Proof. exact (MK_COMB (@lem5225506 s) (@lem5225514 s)). Qed.
Lemma lem5225516 (s : real -> Prop) : (term147 s) = (term159 s).
Proof. exact (EQ_MP (@lem5225515 s) (@lem5225493 s)). Qed.
Lemma lem5225518 {A : Type'} (P : Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5225519 (P : Prop) (Q : real -> Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem5225518 real P Q). Qed.
Lemma lem5225520 (s : real -> Prop) (a : real) : (term164 s a) = (term165 s a).
Proof. exact (@lem5225519 (term62 s a) (term143 s a)). Qed.
Lemma lem5225521 (s : real -> Prop) (x : real) (a : real) : (term166 s a x) = (term141 s x a).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5225522 (s : real -> Prop) (a : real) : (term167 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5225521 s x a)). Qed.
Lemma lem5225523 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225524 (s : real -> Prop) (a : real) : (term168 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5225523) (@lem5225522 s a)). Qed.
Lemma lem5225525 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5225526 (s : real -> Prop) (a : real) : (term164 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5225525 s a) (@lem5225524 s a)). Qed.
Lemma lem5225527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225528 (s : real -> Prop) (a : real) : (term169 s a) = (term170 s a).
Proof. exact (MK_COMB (@lem5225527) (@lem5225526 s a)). Qed.
Lemma lem5225529 (s : real -> Prop) (x : real) (a : real) : (term166 s a x) = (term141 s x a).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5225530 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5225531 (s : real -> Prop) (x : real) (a : real) : (term171 s a x) = (term172 s x a).
Proof. exact (MK_COMB (@lem5225530 s a) (@lem5225529 s x a)). Qed.
Lemma lem5225532 (s : real -> Prop) (a : real) : (term173 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5225531 s x a)). Qed.
Lemma lem5225533 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225534 (s : real -> Prop) (a : real) : (term165 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5225533) (@lem5225532 s a)). Qed.
Lemma lem5225535 (s : real -> Prop) (a : real) : ((term164 s a) = (term165 s a)) = ((term156 s a) = (term175 s a)).
Proof. exact (MK_COMB (@lem5225528 s a) (@lem5225534 s a)). Qed.
Lemma lem5225536 (s : real -> Prop) (a : real) : (term156 s a) = (term175 s a).
Proof. exact (EQ_MP (@lem5225535 s a) (@lem5225520 s a)). Qed.
Lemma lem5225537 (s : real -> Prop) : (term158 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5225536 s a)). Qed.
Lemma lem5225538 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225539 (s : real -> Prop) : (term159 s) = (term177 s).
Proof. exact (MK_COMB (@lem5225538) (@lem5225537 s)). Qed.
Lemma lem5225540 (s : real -> Prop) : (term147 s) = (term177 s).
Proof. exact (TRANS (@lem5225516 s) (@lem5225539 s)). Qed.
Lemma lem5225541 (s : real -> Prop) : (term129 s) = (term177 s).
Proof. exact (TRANS (@lem5225489 s) (@lem5225540 s)). Qed.
Lemma lem5225542 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225543 (s : real -> Prop) : (term130 s) = (term178 s).
Proof. exact (MK_COMB (@lem5225542 s) (@lem5225541 s)). Qed.
Lemma lem5225545 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5225546 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5225545 real P Q). Qed.
Lemma lem5225547 (s : real -> Prop) : (term179 s) = (term180 s).
Proof. exact (@lem5225546 (term72 s) (term176 s)). Qed.
Lemma lem5225548 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5225549 (s : real -> Prop) : (term182 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5225548 s a)). Qed.
Lemma lem5225550 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225551 (s : real -> Prop) : (term183 s) = (term177 s).
Proof. exact (MK_COMB (@lem5225550) (@lem5225549 s)). Qed.
Lemma lem5225552 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225553 (s : real -> Prop) : (term179 s) = (term178 s).
Proof. exact (MK_COMB (@lem5225552 s) (@lem5225551 s)). Qed.
Lemma lem5225554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225555 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5225554) (@lem5225553 s)). Qed.
Lemma lem5225556 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5225557 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225558 (s : real -> Prop) (a : real) : (term186 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5225557 s) (@lem5225556 s a)). Qed.
Lemma lem5225559 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun a : real => @lem5225558 s a)). Qed.
Lemma lem5225560 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225561 (s : real -> Prop) : (term180 s) = (term190 s).
Proof. exact (MK_COMB (@lem5225560) (@lem5225559 s)). Qed.
Lemma lem5225562 (s : real -> Prop) : ((term179 s) = (term180 s)) = ((term178 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5225555 s) (@lem5225561 s)). Qed.
Lemma lem5225563 (s : real -> Prop) : (term178 s) = (term190 s).
Proof. exact (EQ_MP (@lem5225562 s) (@lem5225547 s)). Qed.
Lemma lem5225565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5225566 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5225565 real P Q). Qed.
Lemma lem5225567 (s : real -> Prop) (a : real) : (term191 s a) = (term192 s a).
Proof. exact (@lem5225566 (term72 s) (term174 s a)). Qed.
Lemma lem5225568 (s : real -> Prop) (x : real) (a : real) : (term193 s a x) = (term172 s x a).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5225569 (s : real -> Prop) (a : real) : (term194 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5225568 s x a)). Qed.
Lemma lem5225570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225571 (s : real -> Prop) (a : real) : (term195 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5225570) (@lem5225569 s a)). Qed.
Lemma lem5225572 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225573 (s : real -> Prop) (a : real) : (term191 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5225572 s) (@lem5225571 s a)). Qed.
Lemma lem5225574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5225575 (s : real -> Prop) (a : real) : (term196 s a) = (term197 s a).
Proof. exact (MK_COMB (@lem5225574) (@lem5225573 s a)). Qed.
Lemma lem5225576 (s : real -> Prop) (x : real) (a : real) : (term193 s a x) = (term172 s x a).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5225577 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225578 (s : real -> Prop) (x : real) (a : real) : (term198 s a x) = (term199 s x a).
Proof. exact (MK_COMB (@lem5225577 s) (@lem5225576 s x a)). Qed.
Lemma lem5225579 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (fun_ext (fun x : real => @lem5225578 s x a)). Qed.
Lemma lem5225580 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225581 (s : real -> Prop) (a : real) : (term192 s a) = (term202 s a).
Proof. exact (MK_COMB (@lem5225580) (@lem5225579 s a)). Qed.
Lemma lem5225582 (s : real -> Prop) (a : real) : ((term191 s a) = (term192 s a)) = ((term187 s a) = (term202 s a)).
Proof. exact (MK_COMB (@lem5225575 s a) (@lem5225581 s a)). Qed.
Lemma lem5225583 (s : real -> Prop) (a : real) : (term187 s a) = (term202 s a).
Proof. exact (EQ_MP (@lem5225582 s a) (@lem5225567 s a)). Qed.
Lemma lem5225584 (s : real -> Prop) : (term189 s) = (term203 s).
Proof. exact (fun_ext (fun a : real => @lem5225583 s a)). Qed.
Lemma lem5225585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5225586 (s : real -> Prop) : (term190 s) = (term204 s).
Proof. exact (MK_COMB (@lem5225585) (@lem5225584 s)). Qed.
Lemma lem5225587 (s : real -> Prop) : (term178 s) = (term204 s).
Proof. exact (TRANS (@lem5225563 s) (@lem5225586 s)). Qed.
Lemma lem5225588 (s : real -> Prop) : (term130 s) = (term204 s).
Proof. exact (TRANS (@lem5225543 s) (@lem5225587 s)). Qed.
Lemma lem5225589 : term131 = term205.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5225588 s)). Qed.
Lemma lem5225590 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5225591 : term132 = term206.
Proof. exact (MK_COMB (@lem5225590) (@lem5225589)). Qed.
Lemma lem5225592 : term89 = term206.
Proof. exact (TRANS (@lem5225416) (@lem5225591)). Qed.
Lemma lem5225593 : term10 = term206.
Proof. exact (TRANS (@lem5225167) (@lem5225592)). Qed.
Lemma lem5225594 (h1 : term10) : term206.
Proof. exact (EQ_MP (@lem5225593) (@lem5225097 h1)). Qed.
Lemma lem5225601 (x : real) (y : real) (z : real) : (term207 x y z) = (term208 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5225602 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5225603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225604 (x : real) (y : real) (z : real) : (term209 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem5225603) (@lem5225601 x y z)). Qed.
Lemma lem5225605 (y : real) (x : real) (z : real) : (term211 y x z) = (term212 y x z).
Proof. exact (MK_COMB (@lem5225604 x y z) (@lem5225602 x z)). Qed.
Lemma lem5225606 (y : real) (x : real) (z : real) : (term31 y x z) = (term211 y x z).
Proof. exact (@lem17265 (term213 x y z) (real_le x z)). Qed.
Lemma lem5225607 (y : real) (x : real) (z : real) : (term31 y x z) = (term212 y x z).
Proof. exact (TRANS (@lem5225606 y x z) (@lem5225605 y x z)). Qed.
Lemma lem5225608 (y : real) (x : real) : (term32 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5225607 y x z)). Qed.
Lemma lem5225609 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225610 (y : real) (x : real) : (term33 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5225609) (@lem5225608 y x)). Qed.
Lemma lem5225611 (x : real) : (term34 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5225610 y x)). Qed.
Lemma lem5225612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225613 (x : real) : (term35 x) = (term217 x).
Proof. exact (MK_COMB (@lem5225612) (@lem5225611 x)). Qed.
Lemma lem5225614 : term36 = term218.
Proof. exact (fun_ext (fun x : real => @lem5225613 x)). Qed.
Lemma lem5225615 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225676 : term37 = term219.
Proof. exact (MK_COMB (@lem5225615) (@lem5225614)). Qed.
Lemma lem5225677 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5225676) (@lem5225098 h1)). Qed.
Lemma lem5225681 (s : real -> Prop) : (term220 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5225683 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5225684 (s : real -> Prop) : (term222 s) = (term223 s).
Proof. exact (MK_COMB (@lem5225683 s) (@lem5225681 s)). Qed.
Lemma lem5225685 (s : real -> Prop) : (term224 s) = (term222 s).
Proof. exact (@lem17045 (@FINITE real s) (term225 s)). Qed.
Lemma lem5225686 (s : real -> Prop) : (term224 s) = (term223 s).
Proof. exact (TRANS (@lem5225685 s) (@lem5225684 s)). Qed.
Lemma lem5225694 (s : real -> Prop) (x : real) : (term23 s x) = (term226 s x).
Proof. exact (@lem17265 (@IN real x s) (term42 s x)). Qed.
Lemma lem5225695 (s : real -> Prop) : (term24 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5225694 s x)). Qed.
Lemma lem5225696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225697 (s : real -> Prop) : (term25 s) = (term228 s).
Proof. exact (MK_COMB (@lem5225696) (@lem5225695 s)). Qed.
Lemma lem5225699 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5225700 (s : real -> Prop) : (term27 s) = (term229 s).
Proof. exact (MK_COMB (@lem5225699 s) (@lem5225697 s)). Qed.
Lemma lem5225701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225702 (s : real -> Prop) : (term230 s) = (term231 s).
Proof. exact (MK_COMB (@lem5225701) (@lem5225686 s)). Qed.
Lemma lem5225703 (s : real -> Prop) : (term232 s) = (term233 s).
Proof. exact (MK_COMB (@lem5225702 s) (@lem5225700 s)). Qed.
Lemma lem5225704 (s : real -> Prop) : (term29 s) = (term232 s).
Proof. exact (@lem17265 (term72 s) (term27 s)). Qed.
Lemma lem5225705 (s : real -> Prop) : (term29 s) = (term233 s).
Proof. exact (TRANS (@lem5225704 s) (@lem5225703 s)). Qed.
Lemma lem5225706 : term30 = term234.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5225705 s)). Qed.
Lemma lem5225707 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5225808 : term17 = term235.
Proof. exact (MK_COMB (@lem5225707) (@lem5225706)). Qed.
Lemma lem5225809 (h1 : term17) : term235.
Proof. exact (EQ_MP (@lem5225808) (@lem5225099 h1)). Qed.
Lemma lem5225810 (s : real -> Prop) (h1 : term204 s) : term204 s.
Proof. exact (h1). Qed.
Lemma lem5225811 (s : real -> Prop) (a : real) (h1 : term202 s a) : term202 s a.
Proof. exact (h1). Qed.
Lemma lem5225812 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term199 s x a.
Proof. exact (h1). Qed.
Lemma lem5225837 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5225838 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5225837 y x z)). Qed.
Lemma lem5225839 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225840 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5225839) (@lem5225838 y x)). Qed.
Lemma lem5225841 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5225840 y x)). Qed.
Lemma lem5225842 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225843 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5225842) (@lem5225841 x)). Qed.
Lemma lem5225844 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5225843 x)). Qed.
Lemma lem5225845 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225846 : term219 = term219.
Proof. exact (MK_COMB (@lem5225845) (@lem5225844)). Qed.
Lemma lem5225847 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5225846) (@lem5225677 h1)). Qed.
Lemma lem5225864 (s : real -> Prop) (x : real) : (term226 s x) = (term226 s x).
Proof. exact (eq_refl (term226 s x)). Qed.
Lemma lem5225865 (s : real -> Prop) : (term227 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5225864 s x)). Qed.
Lemma lem5225866 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225867 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (MK_COMB (@lem5225866) (@lem5225865 s)). Qed.
Lemma lem5225876 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5225877 (s : real -> Prop) : (term229 s) = (term229 s).
Proof. exact (MK_COMB (@lem5225876 s) (@lem5225867 s)). Qed.
Lemma lem5225892 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5225893 (s : real -> Prop) : (term233 s) = (term233 s).
Proof. exact (MK_COMB (@lem5225892 s) (@lem5225877 s)). Qed.
Lemma lem5225894 : term234 = term234.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5225893 s)). Qed.
Lemma lem5225895 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5225896 : term235 = term235.
Proof. exact (MK_COMB (@lem5225895) (@lem5225894)). Qed.
Lemma lem5225897 (h1 : term17) : term235.
Proof. exact (EQ_MP (@lem5225896) (@lem5225809 h1)). Qed.
Lemma lem5225922 (s : real -> Prop) (x : real) (a : real) : (term141 s x a) = (term141 s x a).
Proof. exact (eq_refl (term141 s x a)). Qed.
Lemma lem5225939 (s : real -> Prop) (x : real) (a : real) : (term48 s x a) = (term48 s x a).
Proof. exact (eq_refl (term48 s x a)). Qed.
Lemma lem5225940 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5225939 s x a)). Qed.
Lemma lem5225941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5225942 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5225941) (@lem5225940 s a)). Qed.
Lemma lem5225951 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (eq_refl (term60 s a)). Qed.
Lemma lem5225952 (s : real -> Prop) (a : real) : (term62 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5225951 s a) (@lem5225942 s a)). Qed.
Lemma lem5225953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5225954 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5225953) (@lem5225952 s a)). Qed.
Lemma lem5225955 (s : real -> Prop) (x : real) (a : real) : (term172 s x a) = (term172 s x a).
Proof. exact (MK_COMB (@lem5225954 s a) (@lem5225922 s x a)). Qed.
Lemma lem5225970 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5225971 (s : real -> Prop) (x : real) (a : real) : (term199 s x a) = (term199 s x a).
Proof. exact (MK_COMB (@lem5225970 s) (@lem5225955 s x a)). Qed.
Lemma lem5225972 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term199 s x a.
Proof. exact (EQ_MP (@lem5225971 s x a) (@lem5225812 s x a h1)). Qed.
Lemma lem5225973 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term172 s x a.
Proof. exact (proj2 (@lem5225972 s x a h1)). Qed.
Lemma lem5225974 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term72 s.
Proof. exact (proj1 (@lem5225972 s x a h1)). Qed.
Lemma lem5225977 (s : real -> Prop) (a : real) (h1 : term62 s a) : term62 s a.
Proof. exact (h1). Qed.
Lemma lem5225978 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term141 s x a.
Proof. exact (h1). Qed.
Lemma lem5225979 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (proj2 (@lem5225977 s a h1)). Qed.
Lemma lem5225981 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term38 s x a.
Proof. exact (proj2 (@lem5225978 s x a h1)). Qed.
Lemma lem5226011 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5226012 (P : Prop) (Q : real -> Prop) : (term238 P Q) = (term239 P Q).
Proof. exact (@lem5226011 real P Q). Qed.
Lemma lem5226013 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (@lem5226012 (term242 s) (term227 s)). Qed.
Lemma lem5226014 (s : real -> Prop) (x : real) : (term243 s x) = (term226 s x).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5226015 (s : real -> Prop) : (term244 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5226014 s x)). Qed.
Lemma lem5226016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226017 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (MK_COMB (@lem5226016) (@lem5226015 s)). Qed.
Lemma lem5226018 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5226019 (s : real -> Prop) : (term240 s) = (term229 s).
Proof. exact (MK_COMB (@lem5226018 s) (@lem5226017 s)). Qed.
Lemma lem5226020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226021 (s : real -> Prop) : (term246 s) = (term247 s).
Proof. exact (MK_COMB (@lem5226020) (@lem5226019 s)). Qed.
Lemma lem5226022 (s : real -> Prop) (x : real) : (term243 s x) = (term226 s x).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5226023 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5226024 (s : real -> Prop) (x : real) : (term248 s x) = (term249 s x).
Proof. exact (MK_COMB (@lem5226023 s) (@lem5226022 s x)). Qed.
Lemma lem5226025 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5226024 s x)). Qed.
Lemma lem5226026 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226027 (s : real -> Prop) : (term241 s) = (term252 s).
Proof. exact (MK_COMB (@lem5226026) (@lem5226025 s)). Qed.
Lemma lem5226028 (s : real -> Prop) : ((term240 s) = (term241 s)) = ((term229 s) = (term252 s)).
Proof. exact (MK_COMB (@lem5226021 s) (@lem5226027 s)). Qed.
Lemma lem5226029 (s : real -> Prop) : (term229 s) = (term252 s).
Proof. exact (EQ_MP (@lem5226028 s) (@lem5226013 s)). Qed.
Lemma lem5226030 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5226031 (s : real -> Prop) : (term233 s) = (term253 s).
Proof. exact (MK_COMB (@lem5226030 s) (@lem5226029 s)). Qed.
Lemma lem5226033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5226034 (P : Prop) (Q : real -> Prop) : (term256 P Q) = (term257 P Q).
Proof. exact (@lem5226033 real P Q). Qed.
Lemma lem5226035 (s : real -> Prop) : (term258 s) = (term259 s).
Proof. exact (@lem5226034 (term223 s) (term251 s)). Qed.
Lemma lem5226036 (s : real -> Prop) (x : real) : (term260 s x) = (term249 s x).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5226037 (s : real -> Prop) : (term261 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5226036 s x)). Qed.
Lemma lem5226038 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226039 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (MK_COMB (@lem5226038) (@lem5226037 s)). Qed.
Lemma lem5226040 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5226041 (s : real -> Prop) : (term258 s) = (term253 s).
Proof. exact (MK_COMB (@lem5226040 s) (@lem5226039 s)). Qed.
Lemma lem5226042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226043 (s : real -> Prop) : (term263 s) = (term264 s).
Proof. exact (MK_COMB (@lem5226042) (@lem5226041 s)). Qed.
Lemma lem5226044 (s : real -> Prop) (x : real) : (term260 s x) = (term249 s x).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5226045 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5226046 (s : real -> Prop) (x : real) : (term265 s x) = (term266 s x).
Proof. exact (MK_COMB (@lem5226045 s) (@lem5226044 s x)). Qed.
Lemma lem5226047 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (fun_ext (fun x : real => @lem5226046 s x)). Qed.
Lemma lem5226048 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226049 (s : real -> Prop) : (term259 s) = (term269 s).
Proof. exact (MK_COMB (@lem5226048) (@lem5226047 s)). Qed.
Lemma lem5226050 (s : real -> Prop) : ((term258 s) = (term259 s)) = ((term253 s) = (term269 s)).
Proof. exact (MK_COMB (@lem5226043 s) (@lem5226049 s)). Qed.
Lemma lem5226051 (s : real -> Prop) : (term253 s) = (term269 s).
Proof. exact (EQ_MP (@lem5226050 s) (@lem5226035 s)). Qed.
Lemma lem5226052 (s : real -> Prop) : (term233 s) = (term269 s).
Proof. exact (TRANS (@lem5226031 s) (@lem5226051 s)). Qed.
Lemma lem5226053 : term234 = term270.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5226052 s)). Qed.
Lemma lem5226054 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5226055 : term235 = term271.
Proof. exact (MK_COMB (@lem5226054) (@lem5226053)). Qed.
Lemma lem5226084 (s : real -> Prop) (x : real) : (term266 s x) = (term272 s x).
Proof. exact (@lem19490 (term242 s) (term223 s) (term226 s x)). Qed.
Lemma lem5226085 (s : real -> Prop) : (term268 s) = (term273 s).
Proof. exact (fun_ext (fun x : real => @lem5226084 s x)). Qed.
Lemma lem5226086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226087 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (MK_COMB (@lem5226086) (@lem5226085 s)). Qed.
Lemma lem5226088 : term270 = term275.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5226087 s)). Qed.
Lemma lem5226089 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5226090 : term271 = term276.
Proof. exact (MK_COMB (@lem5226089) (@lem5226088)). Qed.
Lemma lem5226091 : term235 = term276.
Proof. exact (TRANS (@lem5226055) (@lem5226090)). Qed.
Lemma lem5226092 (h1 : term17) : term276.
Proof. exact (EQ_MP (@lem5226091) (@lem5225897 h1)). Qed.
Lemma lem5226112 (s : real -> Prop) (x : real) (a : real) : (term48 s x a) = (term48 s x a).
Proof. exact (eq_refl (term48 s x a)). Qed.
Lemma lem5226113 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5226112 s x a)). Qed.
Lemma lem5226114 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226116 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5226114) (@lem5226113 s a)). Qed.
Lemma lem5226117 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (EQ_MP (@lem5226116 s a) (@lem5225979 s a h1)). Qed.
Lemma lem5226131 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5226132 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5226131 y x z)). Qed.
Lemma lem5226133 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226134 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5226133) (@lem5226132 y x)). Qed.
Lemma lem5226135 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5226134 y x)). Qed.
Lemma lem5226136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226137 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5226136) (@lem5226135 x)). Qed.
Lemma lem5226138 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5226137 x)). Qed.
Lemma lem5226139 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226141 : term219 = term219.
Proof. exact (MK_COMB (@lem5226139) (@lem5226138)). Qed.
Lemma lem5226142 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5226141) (@lem5225847 h1)). Qed.
Lemma lem5226144 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5226145 (P : Prop) (Q : real -> Prop) : (term238 P Q) = (term239 P Q).
Proof. exact (@lem5226144 real P Q). Qed.
Lemma lem5226146 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (@lem5226145 (term242 s) (term227 s)). Qed.
Lemma lem5226147 (s : real -> Prop) (x : real) : (term243 s x) = (term226 s x).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5226148 (s : real -> Prop) : (term244 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5226147 s x)). Qed.
Lemma lem5226149 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226150 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (MK_COMB (@lem5226149) (@lem5226148 s)). Qed.
Lemma lem5226151 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5226152 (s : real -> Prop) : (term240 s) = (term229 s).
Proof. exact (MK_COMB (@lem5226151 s) (@lem5226150 s)). Qed.
Lemma lem5226153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226154 (s : real -> Prop) : (term246 s) = (term247 s).
Proof. exact (MK_COMB (@lem5226153) (@lem5226152 s)). Qed.
Lemma lem5226155 (s : real -> Prop) (x : real) : (term243 s x) = (term226 s x).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5226156 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5226157 (s : real -> Prop) (x : real) : (term248 s x) = (term249 s x).
Proof. exact (MK_COMB (@lem5226156 s) (@lem5226155 s x)). Qed.
Lemma lem5226158 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5226157 s x)). Qed.
Lemma lem5226159 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226160 (s : real -> Prop) : (term241 s) = (term252 s).
Proof. exact (MK_COMB (@lem5226159) (@lem5226158 s)). Qed.
Lemma lem5226161 (s : real -> Prop) : ((term240 s) = (term241 s)) = ((term229 s) = (term252 s)).
Proof. exact (MK_COMB (@lem5226154 s) (@lem5226160 s)). Qed.
Lemma lem5226162 (s : real -> Prop) : (term229 s) = (term252 s).
Proof. exact (EQ_MP (@lem5226161 s) (@lem5226146 s)). Qed.
Lemma lem5226163 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5226164 (s : real -> Prop) : (term233 s) = (term253 s).
Proof. exact (MK_COMB (@lem5226163 s) (@lem5226162 s)). Qed.
Lemma lem5226166 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5226167 (P : Prop) (Q : real -> Prop) : (term256 P Q) = (term257 P Q).
Proof. exact (@lem5226166 real P Q). Qed.
Lemma lem5226168 (s : real -> Prop) : (term258 s) = (term259 s).
Proof. exact (@lem5226167 (term223 s) (term251 s)). Qed.
Lemma lem5226169 (s : real -> Prop) (x : real) : (term260 s x) = (term249 s x).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5226170 (s : real -> Prop) : (term261 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5226169 s x)). Qed.
Lemma lem5226171 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226172 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (MK_COMB (@lem5226171) (@lem5226170 s)). Qed.
Lemma lem5226173 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5226174 (s : real -> Prop) : (term258 s) = (term253 s).
Proof. exact (MK_COMB (@lem5226173 s) (@lem5226172 s)). Qed.
Lemma lem5226175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226176 (s : real -> Prop) : (term263 s) = (term264 s).
Proof. exact (MK_COMB (@lem5226175) (@lem5226174 s)). Qed.
Lemma lem5226177 (s : real -> Prop) (x : real) : (term260 s x) = (term249 s x).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5226178 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5226179 (s : real -> Prop) (x : real) : (term265 s x) = (term266 s x).
Proof. exact (MK_COMB (@lem5226178 s) (@lem5226177 s x)). Qed.
Lemma lem5226180 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (fun_ext (fun x : real => @lem5226179 s x)). Qed.
Lemma lem5226181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226182 (s : real -> Prop) : (term259 s) = (term269 s).
Proof. exact (MK_COMB (@lem5226181) (@lem5226180 s)). Qed.
Lemma lem5226183 (s : real -> Prop) : ((term258 s) = (term259 s)) = ((term253 s) = (term269 s)).
Proof. exact (MK_COMB (@lem5226176 s) (@lem5226182 s)). Qed.
Lemma lem5226184 (s : real -> Prop) : (term253 s) = (term269 s).
Proof. exact (EQ_MP (@lem5226183 s) (@lem5226168 s)). Qed.
Lemma lem5226185 (s : real -> Prop) : (term233 s) = (term269 s).
Proof. exact (TRANS (@lem5226164 s) (@lem5226184 s)). Qed.
Lemma lem5226186 : term234 = term270.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5226185 s)). Qed.
Lemma lem5226187 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5226188 : term235 = term271.
Proof. exact (MK_COMB (@lem5226187) (@lem5226186)). Qed.
Lemma lem5226217 (s : real -> Prop) (x : real) : (term266 s x) = (term272 s x).
Proof. exact (@lem19490 (term242 s) (term223 s) (term226 s x)). Qed.
Lemma lem5226218 (s : real -> Prop) : (term268 s) = (term273 s).
Proof. exact (fun_ext (fun x : real => @lem5226217 s x)). Qed.
Lemma lem5226219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5226220 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (MK_COMB (@lem5226219) (@lem5226218 s)). Qed.
Lemma lem5226221 : term270 = term275.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5226220 s)). Qed.
Lemma lem5226222 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5226223 : term271 = term276.
Proof. exact (MK_COMB (@lem5226222) (@lem5226221)). Qed.
Lemma lem5226224 : term235 = term276.
Proof. exact (TRANS (@lem5226188) (@lem5226223)). Qed.
Lemma lem5226225 (h1 : term17) : term276.
Proof. exact (EQ_MP (@lem5226224) (@lem5225897 h1)). Qed.
Lemma lem5226255 (_68400 : real -> Prop) (h1 : term17) : term277 _68400.
Proof. exact (@lem5226092 h1 _68400). Qed.
Lemma lem5226256 (_68400 : real -> Prop) : (term277 _68400) = (term274 _68400).
Proof. exact (eq_refl (term277 _68400)). Qed.
Lemma lem5226257 (_68400 : real -> Prop) (h1 : term17) : term274 _68400.
Proof. exact (EQ_MP (@lem5226256 _68400) (@lem5226255 _68400 h1)). Qed.
Lemma lem5226258 (_68400 : real -> Prop) (_68401 : real) (h1 : term17) : term278 _68400 _68401.
Proof. exact (@lem5226257 _68400 h1 _68401). Qed.
Lemma lem5226259 (_68400 : real -> Prop) (_68401 : real) : (term278 _68400 _68401) = (term272 _68400 _68401).
Proof. exact (eq_refl (term278 _68400 _68401)). Qed.
Lemma lem5226260 (_68400 : real -> Prop) (_68401 : real) (h1 : term17) : term272 _68400 _68401.
Proof. exact (EQ_MP (@lem5226259 _68400 _68401) (@lem5226258 _68400 _68401 h1)). Qed.
Lemma lem5226261 (_68402 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term279 s a _68402.
Proof. exact (@lem5226117 s a h1 _68402). Qed.
Lemma lem5226262 (s : real -> Prop) (_68402 : real) (a : real) : (term279 s a _68402) = (term48 s _68402 a).
Proof. exact (eq_refl (term279 s a _68402)). Qed.
Lemma lem5226264 (_68403 : real) (h1 : term37) : term280 _68403.
Proof. exact (@lem5226142 h1 _68403). Qed.
Lemma lem5226265 (_68403 : real) : (term280 _68403) = (term217 _68403).
Proof. exact (eq_refl (term280 _68403)). Qed.
Lemma lem5226266 (_68403 : real) (h1 : term37) : term217 _68403.
Proof. exact (EQ_MP (@lem5226265 _68403) (@lem5226264 _68403 h1)). Qed.
Lemma lem5226267 (_68403 : real) (_68404 : real) (h1 : term37) : term281 _68403 _68404.
Proof. exact (@lem5226266 _68403 h1 _68404). Qed.
Lemma lem5226268 (_68404 : real) (_68403 : real) : (term281 _68403 _68404) = (term215 _68404 _68403).
Proof. exact (eq_refl (term281 _68403 _68404)). Qed.
Lemma lem5226269 (_68404 : real) (_68403 : real) (h1 : term37) : term215 _68404 _68403.
Proof. exact (EQ_MP (@lem5226268 _68404 _68403) (@lem5226267 _68403 _68404 h1)). Qed.
Lemma lem5226270 (_68404 : real) (_68403 : real) (_68405 : real) (h1 : term37) : term282 _68404 _68403 _68405.
Proof. exact (@lem5226269 _68404 _68403 h1 _68405). Qed.
Lemma lem5226271 (_68404 : real) (_68403 : real) (_68405 : real) : (term282 _68404 _68403 _68405) = (term212 _68404 _68403 _68405).
Proof. exact (eq_refl (term282 _68404 _68403 _68405)). Qed.
Lemma lem5226272 (_68404 : real) (_68403 : real) (_68405 : real) (h1 : term37) : term212 _68404 _68403 _68405.
Proof. exact (EQ_MP (@lem5226271 _68404 _68403 _68405) (@lem5226270 _68404 _68403 _68405 h1)). Qed.
Lemma lem5226273 (_68406 : real -> Prop) (h1 : term17) : term277 _68406.
Proof. exact (@lem5226225 h1 _68406). Qed.
Lemma lem5226274 (_68406 : real -> Prop) : (term277 _68406) = (term274 _68406).
Proof. exact (eq_refl (term277 _68406)). Qed.
Lemma lem5226275 (_68406 : real -> Prop) (h1 : term17) : term274 _68406.
Proof. exact (EQ_MP (@lem5226274 _68406) (@lem5226273 _68406 h1)). Qed.
Lemma lem5226276 (_68406 : real -> Prop) (_68407 : real) (h1 : term17) : term278 _68406 _68407.
Proof. exact (@lem5226275 _68406 h1 _68407). Qed.
Lemma lem5226277 (_68406 : real -> Prop) (_68407 : real) : (term278 _68406 _68407) = (term272 _68406 _68407).
Proof. exact (eq_refl (term278 _68406 _68407)). Qed.
Lemma lem5226278 (_68406 : real -> Prop) (_68407 : real) (h1 : term17) : term272 _68406 _68407.
Proof. exact (EQ_MP (@lem5226277 _68406 _68407) (@lem5226276 _68406 _68407 h1)). Qed.
Lemma lem5226280 (_68400 : real -> Prop) (h1 : term17) : term283 _68400.
Proof. exact (proj1 (@lem5226260 _68400 (@el real) h1)). Qed.
Lemma lem5226281 (_68406 : real -> Prop) (_68407 : real) (h1 : term17) : term284 _68406 _68407.
Proof. exact (proj2 (@lem5226278 _68406 _68407 h1)). Qed.
Lemma lem5226298 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term225 s.
Proof. exact (proj2 (@lem5225974 s x a h1)). Qed.
Lemma lem5226306 (_68402 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term48 s _68402 a.
Proof. exact (EQ_MP (@lem5226262 s _68402 a) (@lem5226261 _68402 s a h1)). Qed.
Lemma lem5226317 (_68400 : real -> Prop) : (term283 _68400) = (term285 _68400).
Proof. exact (@lem5224808 (term286 _68400) (_68400 = (@EMPTY real)) (term242 _68400)). Qed.
Lemma lem5226318 (_68400 : real -> Prop) (h1 : term17) : term285 _68400.
Proof. exact (EQ_MP (@lem5226317 _68400) (@lem5226280 _68400 h1)). Qed.
Lemma lem5226345 (_68404 : real) (_68403 : real) (_68405 : real) : (term212 _68404 _68403 _68405) = (term287 _68404 _68403 _68405).
Proof. exact (@lem5224808 (term288 _68403 _68404) (term288 _68404 _68405) (real_le _68403 _68405)). Qed.
Lemma lem5226346 (_68404 : real) (_68403 : real) (_68405 : real) (h1 : term37) : term287 _68404 _68403 _68405.
Proof. exact (EQ_MP (@lem5226345 _68404 _68403 _68405) (@lem5226272 _68404 _68403 _68405 h1)). Qed.
Lemma lem5226352 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term135 s a.
Proof. exact (proj1 (@lem5225978 s x a h1)). Qed.
Lemma lem5226383 (_68406 : real -> Prop) (_68407 : real) : (term284 _68406 _68407) = (term289 _68406 _68407).
Proof. exact (@lem5224808 (term286 _68406) (_68406 = (@EMPTY real)) (term226 _68406 _68407)). Qed.
Lemma lem5226384 (_68406 : real -> Prop) (_68407 : real) (h1 : term17) : term289 _68406 _68407.
Proof. exact (EQ_MP (@lem5226383 _68406 _68407) (@lem5226281 _68406 _68407 h1)). Qed.
Lemma lem5226448 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (proj1 (@lem5225974 s x a h1)). Qed.
Lemma lem5226449 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term290 s.
Proof. exact (fun h0 : term286 s => @lem5226448 s x a h1). Qed.
Lemma lem5226451 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226452 (s : real -> Prop) : (term290 s) = (@FINITE real s).
Proof. exact (@lem5226451 (@FINITE real s)). Qed.
Lemma lem5226453 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5226452 s) (@lem5226449 s x a h1)). Qed.
Lemma lem5226455 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 s a.
Proof. exact (proj1 (@lem5225977 s a h1)). Qed.
Lemma lem5226456 (s : real -> Prop) (a : real) (h1 : term62 s a) : term292 s a.
Proof. exact (fun h0 : term135 s a => @lem5226455 s a h1). Qed.
Lemma lem5226458 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226459 (s : real -> Prop) (a : real) : (term292 s a) = (term42 s a).
Proof. exact (@lem5226458 (term42 s a)). Qed.
Lemma lem5226460 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 s a.
Proof. exact (EQ_MP (@lem5226459 s a) (@lem5226456 s a h1)). Qed.
Lemma lem5226462 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5226463 (a : real) (_68402 : real) (s : real -> Prop) : (term48 s _68402 a) = (term294 a _68402 s).
Proof. exact (@lem5226462 (term288 _68402 a) (term295 _68402 s)). Qed.
Lemma lem5226465 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5226466 (_68402 : real) (a : real) : (term297 _68402 a) = (real_le _68402 a).
Proof. exact (@lem5226465 (real_le _68402 a)). Qed.
Lemma lem5226467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5226468 (_68402 : real) (a : real) : (term298 _68402 a) = (term299 _68402 a).
Proof. exact (MK_COMB (@lem5226467) (@lem5226466 _68402 a)). Qed.
Lemma lem5226469 (_68402 : real) (s : real -> Prop) : (term295 _68402 s) = (term295 _68402 s).
Proof. exact (eq_refl (term295 _68402 s)). Qed.
Lemma lem5226470 (a : real) (_68402 : real) (s : real -> Prop) : (term294 a _68402 s) = (term300 a _68402 s).
Proof. exact (MK_COMB (@lem5226468 _68402 a) (@lem5226469 _68402 s)). Qed.
Lemma lem5226471 (a : real) (_68402 : real) (s : real -> Prop) : (term48 s _68402 a) = (term300 a _68402 s).
Proof. exact (TRANS (@lem5226463 a _68402 s) (@lem5226470 a _68402 s)). Qed.
Lemma lem5226474 (_68402 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term300 a _68402 s.
Proof. exact (EQ_MP (@lem5226471 a _68402 s) (@lem5226306 _68402 s a h1)). Qed.
Lemma lem5226475 (s : real -> Prop) (a : real) (h1 : term62 s a) : term301 a s.
Proof. exact (@lem5226474 (inf s) s a h1). Qed.
Lemma lem5226478 (s : real -> Prop) (a : real) (h1 : term62 s a) : term302 s.
Proof. exact (@lem5226475 s a h1 (@lem5226460 s a h1)). Qed.
Lemma lem5226479 (s : real -> Prop) (a : real) (h1 : term62 s a) : term303 s.
Proof. exact (fun h0 : term242 s => @lem5226478 s a h1). Qed.
Lemma lem5226481 (p : Prop) : (term304 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5226482 (s : real -> Prop) : (term303 s) = (term302 s).
Proof. exact (@lem5226481 (term242 s)). Qed.
Lemma lem5226483 (s : real -> Prop) (a : real) (h1 : term62 s a) : term302 s.
Proof. exact (EQ_MP (@lem5226482 s) (@lem5226479 s a h1)). Qed.
Lemma lem5226489 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5226490 (_68400 : real -> Prop) : (term285 _68400) = (term305 _68400).
Proof. exact (@lem5226489 (_68400 = (@EMPTY real)) (term286 _68400) (term242 _68400)). Qed.
Lemma lem5226506 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5226507 (_68400 : real -> Prop) : (term306 _68400) = (term307 _68400).
Proof. exact (@lem5226506 (term242 _68400) (term286 _68400)). Qed.
Lemma lem5226513 (_68400 : real -> Prop) : (term308 _68400) = (term308 _68400).
Proof. exact (eq_refl (term308 _68400)). Qed.
Lemma lem5226514 (_68400 : real -> Prop) : (term305 _68400) = (term309 _68400).
Proof. exact (MK_COMB (@lem5226513 _68400) (@lem5226507 _68400)). Qed.
Lemma lem5226525 (_68400 : real -> Prop) : (term285 _68400) = (term309 _68400).
Proof. exact (TRANS (@lem5226490 _68400) (@lem5226514 _68400)). Qed.
Lemma lem5226526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226527 (_68400 : real -> Prop) : (term310 _68400) = (term311 _68400).
Proof. exact (MK_COMB (@lem5226526) (@lem5226525 _68400)). Qed.
Lemma lem5226543 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5226544 (_68400 : real -> Prop) : (term306 _68400) = (term307 _68400).
Proof. exact (@lem5226543 (term242 _68400) (term286 _68400)). Qed.
Lemma lem5226550 (_68400 : real -> Prop) : (term308 _68400) = (term308 _68400).
Proof. exact (eq_refl (term308 _68400)). Qed.
Lemma lem5226551 (_68400 : real -> Prop) : (term305 _68400) = (term309 _68400).
Proof. exact (MK_COMB (@lem5226550 _68400) (@lem5226544 _68400)). Qed.
Lemma lem5226562 (_68400 : real -> Prop) : ((term285 _68400) = (term305 _68400)) = ((term309 _68400) = (term309 _68400)).
Proof. exact (MK_COMB (@lem5226527 _68400) (@lem5226551 _68400)). Qed.
Lemma lem5226564 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5226565 (x : Prop) : (x = x) = True.
Proof. exact (@lem5226564 Prop x). Qed.
Lemma lem5226566 (_68400 : real -> Prop) : ((term309 _68400) = (term309 _68400)) = True.
Proof. exact (@lem5226565 (term309 _68400)). Qed.
Lemma lem5226567 (_68400 : real -> Prop) : ((term285 _68400) = (term305 _68400)) = True.
Proof. exact (TRANS (@lem5226562 _68400) (@lem5226566 _68400)). Qed.
Lemma lem5226568 (_68400 : real -> Prop) : True = ((term285 _68400) = (term305 _68400)).
Proof. exact (SYM (@lem5226567 _68400)). Qed.
Lemma lem5226569 (_68400 : real -> Prop) : (term285 _68400) = (term305 _68400).
Proof. exact (EQ_MP (@lem5226568 _68400) (@lem0)). Qed.
Lemma lem5226570 (_68400 : real -> Prop) (h1 : term17) : term305 _68400.
Proof. exact (EQ_MP (@lem5226569 _68400) (@lem5226318 _68400 h1)). Qed.
Lemma lem5226572 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5226573 (_68400 : real -> Prop) : (term305 _68400) = (term312 _68400).
Proof. exact (@lem5226572 (term306 _68400) (_68400 = (@EMPTY real))). Qed.
Lemma lem5226575 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5226576 (_68400 : real -> Prop) : (term315 _68400) = (term316 _68400).
Proof. exact (@lem5226575 (term286 _68400) (term242 _68400)). Qed.
Lemma lem5226578 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5226579 (_68400 : real -> Prop) : (term317 _68400) = (@FINITE real _68400).
Proof. exact (@lem5226578 (@FINITE real _68400)). Qed.
Lemma lem5226580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5226581 (_68400 : real -> Prop) : (term318 _68400) = (term319 _68400).
Proof. exact (MK_COMB (@lem5226580) (@lem5226579 _68400)). Qed.
Lemma lem5226582 (_68400 : real -> Prop) : (term302 _68400) = (term302 _68400).
Proof. exact (eq_refl (term302 _68400)). Qed.
Lemma lem5226583 (_68400 : real -> Prop) : (term316 _68400) = (term320 _68400).
Proof. exact (MK_COMB (@lem5226581 _68400) (@lem5226582 _68400)). Qed.
Lemma lem5226584 (_68400 : real -> Prop) : (term315 _68400) = (term320 _68400).
Proof. exact (TRANS (@lem5226576 _68400) (@lem5226583 _68400)). Qed.
Lemma lem5226585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5226586 (_68400 : real -> Prop) : (term321 _68400) = (term322 _68400).
Proof. exact (MK_COMB (@lem5226585) (@lem5226584 _68400)). Qed.
Lemma lem5226587 (_68400 : real -> Prop) : (_68400 = (@EMPTY real)) = (_68400 = (@EMPTY real)).
Proof. exact (eq_refl (_68400 = (@EMPTY real))). Qed.
Lemma lem5226588 (_68400 : real -> Prop) : (term312 _68400) = (term323 _68400).
Proof. exact (MK_COMB (@lem5226586 _68400) (@lem5226587 _68400)). Qed.
Lemma lem5226589 (_68400 : real -> Prop) : (term305 _68400) = (term323 _68400).
Proof. exact (TRANS (@lem5226573 _68400) (@lem5226588 _68400)). Qed.
Lemma lem5226591 (x : real) (s : real -> Prop) (a : real) (h1 : term199 s x a) (h2 : term62 s a) : term320 s.
Proof. exact (conj (@lem5226453 s x a h1) (@lem5226483 s a h2)). Qed.
Lemma lem5226593 (_68400 : real -> Prop) (h1 : term17) : term323 _68400.
Proof. exact (EQ_MP (@lem5226589 _68400) (@lem5226570 _68400 h1)). Qed.
Lemma lem5226594 (s : real -> Prop) (h1 : term17) : term323 s.
Proof. exact (@lem5226593 s h1). Qed.
Lemma lem5226597 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (@lem5226594 s h1 (@lem5226591 x s a h2 h3)). Qed.
Lemma lem5226598 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : term324 s.
Proof. exact (fun h0 : term225 s => @lem5226597 x s a h1 h2 h3). Qed.
Lemma lem5226600 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226601 (s : real -> Prop) : (term324 s) = (s = (@EMPTY real)).
Proof. exact (@lem5226600 (s = (@EMPTY real))). Qed.
Lemma lem5226602 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5226601 s) (@lem5226598 x s a h1 h2 h3)). Qed.
Lemma lem5226605 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5226607 (s : real -> Prop) : (term225 s) = (term325 s).
Proof. exact (@lem5226605 (s = (@EMPTY real))). Qed.
Lemma lem5226610 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term325 s.
Proof. exact (EQ_MP (@lem5226607 s) (@lem5226298 s x a h1)). Qed.
Lemma lem5226613 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : False.
Proof. exact (@lem5226610 s x a h2 (@lem5226602 x s a h1 h2 h3)). Qed.
Lemma lem5226614 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : term326.
Proof. exact (fun h0 : ~ False => @lem5226613 x s a h1 h2 h3). Qed.
Lemma lem5226616 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226617 : term326 = False.
Proof. exact (@lem5226616 False). Qed.
Lemma lem5226618 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : False.
Proof. exact (EQ_MP (@lem5226617) (@lem5226614 x s a h1 h2 h3)). Qed.
Lemma lem5226682 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (proj1 (@lem5225974 s x a h1)). Qed.
Lemma lem5226683 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term290 s.
Proof. exact (fun h0 : term286 s => @lem5226682 s x a h1). Qed.
Lemma lem5226685 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226686 (s : real -> Prop) : (term290 s) = (@FINITE real s).
Proof. exact (@lem5226685 (@FINITE real s)). Qed.
Lemma lem5226687 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5226686 s) (@lem5226683 s x a h1)). Qed.
Lemma lem5226689 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term225 s.
Proof. exact (proj2 (@lem5225974 s x a h1)). Qed.
Lemma lem5226690 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term327 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5226689 s x a h1). Qed.
Lemma lem5226692 (p : Prop) : (term304 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5226693 (s : real -> Prop) : (term327 s) = (term225 s).
Proof. exact (@lem5226692 (s = (@EMPTY real))). Qed.
Lemma lem5226694 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term225 s.
Proof. exact (EQ_MP (@lem5226693 s) (@lem5226690 s x a h1)). Qed.
Lemma lem5226696 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : @IN real x s.
Proof. exact (proj1 (@lem5225981 s x a h1)). Qed.
Lemma lem5226697 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term328 x s.
Proof. exact (fun h0 : term295 x s => @lem5226696 s x a h1). Qed.
Lemma lem5226699 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226700 (x : real) (s : real -> Prop) : (term328 x s) = (@IN real x s).
Proof. exact (@lem5226699 (@IN real x s)). Qed.
Lemma lem5226701 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : @IN real x s.
Proof. exact (EQ_MP (@lem5226700 x s) (@lem5226697 s x a h1)). Qed.
Lemma lem5226707 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5226708 (_68406 : real -> Prop) (_68407 : real) : (term289 _68406 _68407) = (term329 _68406 _68407).
Proof. exact (@lem5226707 (_68406 = (@EMPTY real)) (term286 _68406) (term226 _68406 _68407)). Qed.
Lemma lem5226734 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5226735 (_68407 : real) (_68406 : real -> Prop) : (term226 _68406 _68407) = (term330 _68407 _68406).
Proof. exact (@lem5226734 (term42 _68406 _68407) (term295 _68407 _68406)). Qed.
Lemma lem5226741 (_68406 : real -> Prop) : (term221 _68406) = (term221 _68406).
Proof. exact (eq_refl (term221 _68406)). Qed.
Lemma lem5226742 (_68407 : real) (_68406 : real -> Prop) : (term331 _68406 _68407) = (term332 _68407 _68406).
Proof. exact (MK_COMB (@lem5226741 _68406) (@lem5226735 _68407 _68406)). Qed.
Lemma lem5226746 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5226747 (_68407 : real) (_68406 : real -> Prop) : (term332 _68407 _68406) = (term333 _68407 _68406).
Proof. exact (@lem5226746 (term42 _68406 _68407) (term286 _68406) (term295 _68407 _68406)). Qed.
Lemma lem5226763 (_68407 : real) (_68406 : real -> Prop) : (term331 _68406 _68407) = (term333 _68407 _68406).
Proof. exact (TRANS (@lem5226742 _68407 _68406) (@lem5226747 _68407 _68406)). Qed.
Lemma lem5226764 (_68406 : real -> Prop) : (term308 _68406) = (term308 _68406).
Proof. exact (eq_refl (term308 _68406)). Qed.
Lemma lem5226765 (_68407 : real) (_68406 : real -> Prop) : (term329 _68406 _68407) = (term334 _68407 _68406).
Proof. exact (MK_COMB (@lem5226764 _68406) (@lem5226763 _68407 _68406)). Qed.
Lemma lem5226776 (_68407 : real) (_68406 : real -> Prop) : (term289 _68406 _68407) = (term334 _68407 _68406).
Proof. exact (TRANS (@lem5226708 _68406 _68407) (@lem5226765 _68407 _68406)). Qed.
Lemma lem5226777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226778 (_68407 : real) (_68406 : real -> Prop) : (term335 _68406 _68407) = (term336 _68407 _68406).
Proof. exact (MK_COMB (@lem5226777) (@lem5226776 _68407 _68406)). Qed.
Lemma lem5226792 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5226793 (_68407 : real) (_68406 : real -> Prop) : (term337 _68407 _68406) = (term338 _68407 _68406).
Proof. exact (@lem5226792 (_68406 = (@EMPTY real)) (term286 _68406) (term295 _68407 _68406)). Qed.
Lemma lem5226811 (_68406 : real -> Prop) (_68407 : real) : (term339 _68406 _68407) = (term339 _68406 _68407).
Proof. exact (eq_refl (term339 _68406 _68407)). Qed.
Lemma lem5226812 (_68407 : real) (_68406 : real -> Prop) : (term340 _68407 _68406) = (term341 _68407 _68406).
Proof. exact (MK_COMB (@lem5226811 _68406 _68407) (@lem5226793 _68407 _68406)). Qed.
Lemma lem5226816 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5226817 (_68407 : real) (_68406 : real -> Prop) : (term341 _68407 _68406) = (term334 _68407 _68406).
Proof. exact (@lem5226816 (_68406 = (@EMPTY real)) (term42 _68406 _68407) (term342 _68407 _68406)). Qed.
Lemma lem5226845 (_68407 : real) (_68406 : real -> Prop) : (term340 _68407 _68406) = (term334 _68407 _68406).
Proof. exact (TRANS (@lem5226812 _68407 _68406) (@lem5226817 _68407 _68406)). Qed.
Lemma lem5226846 (_68407 : real) (_68406 : real -> Prop) : ((term289 _68406 _68407) = (term340 _68407 _68406)) = ((term334 _68407 _68406) = (term334 _68407 _68406)).
Proof. exact (MK_COMB (@lem5226778 _68407 _68406) (@lem5226845 _68407 _68406)). Qed.
Lemma lem5226848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5226849 (x : Prop) : (x = x) = True.
Proof. exact (@lem5226848 Prop x). Qed.
Lemma lem5226850 (_68407 : real) (_68406 : real -> Prop) : ((term334 _68407 _68406) = (term334 _68407 _68406)) = True.
Proof. exact (@lem5226849 (term334 _68407 _68406)). Qed.
Lemma lem5226851 (_68407 : real) (_68406 : real -> Prop) : ((term289 _68406 _68407) = (term340 _68407 _68406)) = True.
Proof. exact (TRANS (@lem5226846 _68407 _68406) (@lem5226850 _68407 _68406)). Qed.
Lemma lem5226852 (_68407 : real) (_68406 : real -> Prop) : True = ((term289 _68406 _68407) = (term340 _68407 _68406)).
Proof. exact (SYM (@lem5226851 _68407 _68406)). Qed.
Lemma lem5226853 (_68407 : real) (_68406 : real -> Prop) : (term289 _68406 _68407) = (term340 _68407 _68406).
Proof. exact (EQ_MP (@lem5226852 _68407 _68406) (@lem0)). Qed.
Lemma lem5226854 (_68407 : real) (_68406 : real -> Prop) (h1 : term17) : term340 _68407 _68406.
Proof. exact (EQ_MP (@lem5226853 _68407 _68406) (@lem5226384 _68406 _68407 h1)). Qed.
Lemma lem5226856 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5226857 (_68406 : real -> Prop) (_68407 : real) : (term340 _68407 _68406) = (term343 _68406 _68407).
Proof. exact (@lem5226856 (term337 _68407 _68406) (term42 _68406 _68407)). Qed.
Lemma lem5226859 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5226860 (_68407 : real) (_68406 : real -> Prop) : (term344 _68407 _68406) = (term345 _68407 _68406).
Proof. exact (@lem5226859 (term286 _68406) (term346 _68407 _68406)). Qed.
Lemma lem5226862 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5226863 (_68406 : real -> Prop) : (term317 _68406) = (@FINITE real _68406).
Proof. exact (@lem5226862 (@FINITE real _68406)). Qed.
Lemma lem5226864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5226865 (_68406 : real -> Prop) : (term318 _68406) = (term319 _68406).
Proof. exact (MK_COMB (@lem5226864) (@lem5226863 _68406)). Qed.
Lemma lem5226867 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5226868 (_68407 : real) (_68406 : real -> Prop) : (term347 _68407 _68406) = (term348 _68407 _68406).
Proof. exact (@lem5226867 (_68406 = (@EMPTY real)) (term295 _68407 _68406)). Qed.
Lemma lem5226870 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5226871 (_68407 : real) (_68406 : real -> Prop) : (term349 _68407 _68406) = (@IN real _68407 _68406).
Proof. exact (@lem5226870 (@IN real _68407 _68406)). Qed.
Lemma lem5226872 (_68406 : real -> Prop) : (term350 _68406) = (term350 _68406).
Proof. exact (eq_refl (term350 _68406)). Qed.
Lemma lem5226873 (_68407 : real) (_68406 : real -> Prop) : (term348 _68407 _68406) = (term351 _68407 _68406).
Proof. exact (MK_COMB (@lem5226872 _68406) (@lem5226871 _68407 _68406)). Qed.
Lemma lem5226874 (_68407 : real) (_68406 : real -> Prop) : (term347 _68407 _68406) = (term351 _68407 _68406).
Proof. exact (TRANS (@lem5226868 _68407 _68406) (@lem5226873 _68407 _68406)). Qed.
Lemma lem5226875 (_68407 : real) (_68406 : real -> Prop) : (term345 _68407 _68406) = (term352 _68407 _68406).
Proof. exact (MK_COMB (@lem5226865 _68406) (@lem5226874 _68407 _68406)). Qed.
Lemma lem5226876 (_68407 : real) (_68406 : real -> Prop) : (term344 _68407 _68406) = (term352 _68407 _68406).
Proof. exact (TRANS (@lem5226860 _68407 _68406) (@lem5226875 _68407 _68406)). Qed.
Lemma lem5226877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5226878 (_68407 : real) (_68406 : real -> Prop) : (term353 _68407 _68406) = (term354 _68407 _68406).
Proof. exact (MK_COMB (@lem5226877) (@lem5226876 _68407 _68406)). Qed.
Lemma lem5226879 (_68406 : real -> Prop) (_68407 : real) : (term42 _68406 _68407) = (term42 _68406 _68407).
Proof. exact (eq_refl (term42 _68406 _68407)). Qed.
Lemma lem5226880 (_68406 : real -> Prop) (_68407 : real) : (term343 _68406 _68407) = (term355 _68406 _68407).
Proof. exact (MK_COMB (@lem5226878 _68407 _68406) (@lem5226879 _68406 _68407)). Qed.
Lemma lem5226881 (_68406 : real -> Prop) (_68407 : real) : (term340 _68407 _68406) = (term355 _68406 _68407).
Proof. exact (TRANS (@lem5226857 _68406 _68407) (@lem5226880 _68406 _68407)). Qed.
Lemma lem5226883 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) (h2 : term199 s x a) : term351 x s.
Proof. exact (conj (@lem5226694 s x a h2) (@lem5226701 s x a h1)). Qed.
Lemma lem5226884 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) (h2 : term199 s x a) : term352 x s.
Proof. exact (conj (@lem5226687 s x a h2) (@lem5226883 s x a h1 h2)). Qed.
Lemma lem5226886 (_68406 : real -> Prop) (_68407 : real) (h1 : term17) : term355 _68406 _68407.
Proof. exact (EQ_MP (@lem5226881 _68406 _68407) (@lem5226854 _68407 _68406 h1)). Qed.
Lemma lem5226887 (s : real -> Prop) (x : real) (h1 : term17) : term355 s x.
Proof. exact (@lem5226886 s x h1). Qed.
Lemma lem5226890 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term42 s x.
Proof. exact (@lem5226887 s x h1 (@lem5226884 s x a h2 h3)). Qed.
Lemma lem5226891 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term292 s x.
Proof. exact (fun h0 : term135 s x => @lem5226890 s x a h1 h2 h3). Qed.
Lemma lem5226893 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226894 (s : real -> Prop) (x : real) : (term292 s x) = (term42 s x).
Proof. exact (@lem5226893 (term42 s x)). Qed.
Lemma lem5226895 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term42 s x.
Proof. exact (EQ_MP (@lem5226894 s x) (@lem5226891 s x a h1 h2 h3)). Qed.
Lemma lem5226897 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : real_le x a.
Proof. exact (proj2 (@lem5225981 s x a h1)). Qed.
Lemma lem5226898 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term356 x a.
Proof. exact (fun h0 : term288 x a => @lem5226897 s x a h1). Qed.
Lemma lem5226900 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5226901 (x : real) (a : real) : (term356 x a) = (real_le x a).
Proof. exact (@lem5226900 (real_le x a)). Qed.
Lemma lem5226902 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : real_le x a.
Proof. exact (EQ_MP (@lem5226901 x a) (@lem5226898 s x a h1)). Qed.
Lemma lem5226918 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5226919 (_68403 : real) (_68404 : real) (_68405 : real) : (term357 _68404 _68403 _68405) = (term358 _68403 _68404 _68405).
Proof. exact (@lem5226918 (real_le _68403 _68405) (term288 _68404 _68405)). Qed.
Lemma lem5226925 (_68403 : real) (_68404 : real) : (term359 _68403 _68404) = (term359 _68403 _68404).
Proof. exact (eq_refl (term359 _68403 _68404)). Qed.
Lemma lem5226926 (_68403 : real) (_68404 : real) (_68405 : real) : (term287 _68404 _68403 _68405) = (term360 _68403 _68404 _68405).
Proof. exact (MK_COMB (@lem5226925 _68403 _68404) (@lem5226919 _68403 _68404 _68405)). Qed.
Lemma lem5226930 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5226931 (_68403 : real) (_68404 : real) (_68405 : real) : (term360 _68403 _68404 _68405) = (term361 _68403 _68404 _68405).
Proof. exact (@lem5226930 (real_le _68403 _68405) (term288 _68403 _68404) (term288 _68404 _68405)). Qed.
Lemma lem5226947 (_68403 : real) (_68404 : real) (_68405 : real) : (term287 _68404 _68403 _68405) = (term361 _68403 _68404 _68405).
Proof. exact (TRANS (@lem5226926 _68403 _68404 _68405) (@lem5226931 _68403 _68404 _68405)). Qed.
Lemma lem5226948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5226949 (_68403 : real) (_68404 : real) (_68405 : real) : (term362 _68404 _68403 _68405) = (term363 _68403 _68404 _68405).
Proof. exact (MK_COMB (@lem5226948) (@lem5226947 _68403 _68404 _68405)). Qed.
Lemma lem5226965 (_68403 : real) (_68404 : real) (_68405 : real) : (term361 _68403 _68404 _68405) = (term361 _68403 _68404 _68405).
Proof. exact (eq_refl (term361 _68403 _68404 _68405)). Qed.
Lemma lem5226966 (_68403 : real) (_68404 : real) (_68405 : real) : ((term287 _68404 _68403 _68405) = (term361 _68403 _68404 _68405)) = ((term361 _68403 _68404 _68405) = (term361 _68403 _68404 _68405)).
Proof. exact (MK_COMB (@lem5226949 _68403 _68404 _68405) (@lem5226965 _68403 _68404 _68405)). Qed.
Lemma lem5226968 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5226969 (x : Prop) : (x = x) = True.
Proof. exact (@lem5226968 Prop x). Qed.
Lemma lem5226970 (_68403 : real) (_68404 : real) (_68405 : real) : ((term361 _68403 _68404 _68405) = (term361 _68403 _68404 _68405)) = True.
Proof. exact (@lem5226969 (term361 _68403 _68404 _68405)). Qed.
Lemma lem5226971 (_68403 : real) (_68404 : real) (_68405 : real) : ((term287 _68404 _68403 _68405) = (term361 _68403 _68404 _68405)) = True.
Proof. exact (TRANS (@lem5226966 _68403 _68404 _68405) (@lem5226970 _68403 _68404 _68405)). Qed.
Lemma lem5226972 (_68403 : real) (_68404 : real) (_68405 : real) : True = ((term287 _68404 _68403 _68405) = (term361 _68403 _68404 _68405)).
Proof. exact (SYM (@lem5226971 _68403 _68404 _68405)). Qed.
Lemma lem5226973 (_68403 : real) (_68404 : real) (_68405 : real) : (term287 _68404 _68403 _68405) = (term361 _68403 _68404 _68405).
Proof. exact (EQ_MP (@lem5226972 _68403 _68404 _68405) (@lem0)). Qed.
Lemma lem5226974 (_68403 : real) (_68404 : real) (_68405 : real) (h1 : term37) : term361 _68403 _68404 _68405.
Proof. exact (EQ_MP (@lem5226973 _68403 _68404 _68405) (@lem5226346 _68404 _68403 _68405 h1)). Qed.
Lemma lem5226976 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5226977 (_68404 : real) (_68403 : real) (_68405 : real) : (term361 _68403 _68404 _68405) = (term364 _68404 _68403 _68405).
Proof. exact (@lem5226976 (term208 _68403 _68404 _68405) (real_le _68403 _68405)). Qed.
Lemma lem5226979 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5226980 (_68403 : real) (_68404 : real) (_68405 : real) : (term365 _68403 _68404 _68405) = (term366 _68403 _68404 _68405).
Proof. exact (@lem5226979 (term288 _68403 _68404) (term288 _68404 _68405)). Qed.
Lemma lem5226982 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5226983 (_68403 : real) (_68404 : real) : (term297 _68403 _68404) = (real_le _68403 _68404).
Proof. exact (@lem5226982 (real_le _68403 _68404)). Qed.
Lemma lem5226984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5226985 (_68403 : real) (_68404 : real) : (term367 _68403 _68404) = (term368 _68403 _68404).
Proof. exact (MK_COMB (@lem5226984) (@lem5226983 _68403 _68404)). Qed.
Lemma lem5226987 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5226988 (_68404 : real) (_68405 : real) : (term297 _68404 _68405) = (real_le _68404 _68405).
Proof. exact (@lem5226987 (real_le _68404 _68405)). Qed.
Lemma lem5226989 (_68403 : real) (_68404 : real) (_68405 : real) : (term366 _68403 _68404 _68405) = (term213 _68403 _68404 _68405).
Proof. exact (MK_COMB (@lem5226985 _68403 _68404) (@lem5226988 _68404 _68405)). Qed.
Lemma lem5226990 (_68403 : real) (_68404 : real) (_68405 : real) : (term365 _68403 _68404 _68405) = (term213 _68403 _68404 _68405).
Proof. exact (TRANS (@lem5226980 _68403 _68404 _68405) (@lem5226989 _68403 _68404 _68405)). Qed.
Lemma lem5226991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5226992 (_68403 : real) (_68404 : real) (_68405 : real) : (term369 _68403 _68404 _68405) = (term370 _68403 _68404 _68405).
Proof. exact (MK_COMB (@lem5226991) (@lem5226990 _68403 _68404 _68405)). Qed.
Lemma lem5226993 (_68403 : real) (_68405 : real) : (real_le _68403 _68405) = (real_le _68403 _68405).
Proof. exact (eq_refl (real_le _68403 _68405)). Qed.
Lemma lem5226994 (_68404 : real) (_68403 : real) (_68405 : real) : (term364 _68404 _68403 _68405) = (term31 _68404 _68403 _68405).
Proof. exact (MK_COMB (@lem5226992 _68403 _68404 _68405) (@lem5226993 _68403 _68405)). Qed.
Lemma lem5226995 (_68404 : real) (_68403 : real) (_68405 : real) : (term361 _68403 _68404 _68405) = (term31 _68404 _68403 _68405).
Proof. exact (TRANS (@lem5226977 _68404 _68403 _68405) (@lem5226994 _68404 _68403 _68405)). Qed.
Lemma lem5226997 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term371 s x a.
Proof. exact (conj (@lem5226895 s x a h1 h2 h3) (@lem5226902 s x a h2)). Qed.
Lemma lem5226999 (_68404 : real) (_68403 : real) (_68405 : real) (h1 : term37) : term31 _68404 _68403 _68405.
Proof. exact (EQ_MP (@lem5226995 _68404 _68403 _68405) (@lem5226974 _68403 _68404 _68405 h1)). Qed.
Lemma lem5227000 (x : real) (s : real -> Prop) (a : real) (h1 : term37) : term372 x s a.
Proof. exact (@lem5226999 x (inf s) a h1). Qed.
Lemma lem5227003 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term42 s a.
Proof. exact (@lem5227000 x s a h2 (@lem5226997 s x a h1 h3 h4)). Qed.
Lemma lem5227004 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term292 s a.
Proof. exact (fun h0 : term135 s a => @lem5227003 s x a h1 h2 h3 h4). Qed.
Lemma lem5227006 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5227007 (s : real -> Prop) (a : real) : (term292 s a) = (term42 s a).
Proof. exact (@lem5227006 (term42 s a)). Qed.
Lemma lem5227008 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term42 s a.
Proof. exact (EQ_MP (@lem5227007 s a) (@lem5227004 s x a h1 h2 h3 h4)). Qed.
Lemma lem5227011 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5227013 (s : real -> Prop) (a : real) : (term135 s a) = (term373 s a).
Proof. exact (@lem5227011 (term42 s a)). Qed.
Lemma lem5227016 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term373 s a.
Proof. exact (EQ_MP (@lem5227013 s a) (@lem5226352 s x a h1)). Qed.
Lemma lem5227019 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : False.
Proof. exact (@lem5227016 s x a h3 (@lem5227008 s x a h1 h2 h3 h4)). Qed.
Lemma lem5227020 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term326.
Proof. exact (fun h0 : ~ False => @lem5227019 s x a h1 h2 h3 h4). Qed.
Lemma lem5227022 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5227023 : term326 = False.
Proof. exact (@lem5227022 False). Qed.
Lemma lem5227024 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : False.
Proof. exact (EQ_MP (@lem5227023) (@lem5227020 s x a h1 h2 h3 h4)). Qed.
Lemma lem5227025 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term199 s x a) : False.
Proof. exact (or_elim (@lem5225973 s x a h3) (fun h0 : term62 s a => @lem5226618 x s a h1 h3 h0) (fun h0 : term141 s x a => @lem5227024 s x a h1 h2 h0 h3)). Qed.
Lemma lem5227026 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term199 s x a) : (term199 s x a) = False.
Proof. exact (prop_ext (fun h4 : term199 s x a => @lem5227025 s x a h1 h2 h3) (fun h4 : False => @lem5225972 s x a h3)). Qed.
Lemma lem5227027 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term199 s x a) : False.
Proof. exact (EQ_MP (@lem5227026 s x a h1 h2 h3) (@lem5225972 s x a h3)). Qed.
Lemma lem5227028 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term202 s a) : False.
Proof. exact (ex_elim (@lem5225811 s a h3) (fun x : real => fun h0 : term201 s a x => @lem5227027 s x a h1 h2 h0)). Qed.
Lemma lem5227029 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term204 s) : False.
Proof. exact (ex_elim (@lem5225810 s h3) (fun a : real => fun h0 : term203 s a => @lem5227028 s a h1 h2 h0)). Qed.
Lemma lem5227030 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5225594 h3) (fun s : real -> Prop => fun h0 : term205 s => @lem5227029 s h1 h2 h0)). Qed.
Lemma lem5227031 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5227030 h0 h1 h2). Qed.
Lemma lem5227032 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5227033 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5227032) (@lem5227031 h1 h2)). Qed.
Lemma lem5227034 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5227033 h0 h1). Qed.
Lemma lem5227035 : term22.
Proof. exact (fun h0 : term10 => @lem5227034 h0). Qed.
Lemma lem5227036 : term11.
Proof. exact (EQ_MP (@lem5225096) (@lem5227035)). Qed.
Lemma lem5227038 : term11.
Proof. exact (@lem5224828 (@lem5227036)). Qed.
Lemma lem5227039 (h1 : term10) : term19.
Proof. exact (@lem5227038 (@lem5224813 h1)). Qed.
Lemma lem5227040 (h1 : term10) : term15.
Proof. exact (@lem5227039 h1 (@lem1339577)). Qed.
Lemma lem5227041 (h1 : term10) : False.
Proof. exact (@lem5227040 h1 (@lem5222545)). Qed.
Lemma lem5227042 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5227041 h1) (fun h2 : False => @lem5224813 h1)). Qed.
Lemma lem5227043 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5227042 h1) (@lem5224813 h1)). Qed.
Lemma lem5227044 : term9.
Proof. exact (fun h0 : term10 => @lem5227043 h0). Qed.
Lemma lem5227045 : term8.
Proof. exact (EQ_MP (@lem5224812) (@lem5227044)). Qed.
