Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_NEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LE_RNEG_spec.
Require Import REAL_NEG_0_spec.
Require Import REAL_NEG_NEG_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1338512_spec.
Require Import thm1339379_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17784_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1362924 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1362925 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1362926 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1362925 t1) (@lem1362924 t1)). Qed.
Lemma lem1362927 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1362926 t1 t2). Qed.
Lemma lem1362928 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1362929 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1362928 t1 t2) (@lem1362927 t1 t2)). Qed.
Lemma lem1362930 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1362929 t1 t2 t3). Qed.
Lemma lem1362931 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1362932 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1362931 t1 t2 t3) (@lem1362930 t1 t2 t3)). Qed.
Lemma lem1362933 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1362932 t1 t2 t3)). Qed.
Lemma lem1362934 (x : real) : term7 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1362935 (x : real) : (term7 x) = ((term8 x) = x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1362937 (x : real) : term9 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1362938 (x : real) : (term9 x) = ((term10 x) = x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1362940 (x : real) : term11 x.
Proof. exact (@lem1362465 x). Qed.
Lemma lem1362941 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1362942 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1362941 x) (@lem1362940 x)). Qed.
Lemma lem1362943 (x : real) (y : real) : term13 x y.
Proof. exact (@lem1362942 x y). Qed.
Lemma lem1362944 (x : real) (y : real) : (term13 x y) = ((term14 x y) = (term15 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1362946 (x : real) : term16 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1362947 (x : real) : (term16 x) = ((real_abs x) = (term17 x)).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1362956 (x : real) : (real_abs x) = (term17 x).
Proof. exact (EQ_MP (@lem1362947 x) (@lem1362946 x)). Qed.
Lemma lem1362957 (x : real) : (term18 x) = (term19 x).
Proof. exact (@lem1362956 (real_neg x)). Qed.
Lemma lem1362959 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1362944 x y) (@lem1362943 x y)). Qed.
Lemma lem1362960 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1362959 term22 x). Qed.
Lemma lem1362962 (x : real) : (term8 x) = x.
Proof. exact (EQ_MP (@lem1362935 x) (@lem1362934 x)). Qed.
Lemma lem1362963 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1362964 (x : real) : (term23 x) = (real_le x).
Proof. exact (MK_COMB (@lem1362963) (@lem1362962 x)). Qed.
Lemma lem1362965 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1362966 (x : real) : (term21 x) = (term24 x).
Proof. exact (MK_COMB (@lem1362964 x) (@lem1362965)). Qed.
Lemma lem1362967 (x : real) : (term20 x) = (term24 x).
Proof. exact (TRANS (@lem1362960 x) (@lem1362966 x)). Qed.
Lemma lem1362968 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362969 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1362968) (@lem1362967 x)). Qed.
Lemma lem1362970 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1362971 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1362969 x) (@lem1362970 x)). Qed.
Lemma lem1362973 (x : real) : (term10 x) = x.
Proof. exact (EQ_MP (@lem1362938 x) (@lem1362937 x)). Qed.
Lemma lem1362974 (x : real) : (term19 x) = (term29 x).
Proof. exact (MK_COMB (@lem1362971 x) (@lem1362973 x)). Qed.
Lemma lem1362975 (x : real) : (term18 x) = (term29 x).
Proof. exact (TRANS (@lem1362957 x) (@lem1362974 x)). Qed.
Lemma lem1362976 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362977 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1362976) (@lem1362975 x)). Qed.
Lemma lem1362979 (x : real) : (real_abs x) = (term17 x).
Proof. exact (EQ_MP (@lem1362947 x) (@lem1362946 x)). Qed.
Lemma lem1362980 (x : real) : ((term18 x) = (real_abs x)) = ((term29 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1362977 x) (@lem1362979 x)). Qed.
Lemma lem1362983 : term32 = term33.
Proof. exact (fun_ext (fun x : real => @lem1362980 x)). Qed.
Lemma lem1362984 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362985 : term34 = term35.
Proof. exact (MK_COMB (@lem1362984) (@lem1362983)). Qed.
Lemma lem1362990 : term35 = term34.
Proof. exact (SYM (@lem1362985)). Qed.
Lemma lem1362992 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1362993 : term35 = term37.
Proof. exact (@lem1362992 term35). Qed.
Lemma lem1362994 : term37 = term35.
Proof. exact (SYM (@lem1362993)). Qed.
Lemma lem1362995 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1362998 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem1362999 : term40.
Proof. exact (fun h0 : term39 => @lem1362998 h0). Qed.
Lemma lem1363000 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1363001 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem1363002 (h1 : term39) (h2 : term40) : term39.
Proof. exact (@lem1363000 h2 (@lem1363001 h1)). Qed.
Lemma lem1363003 (h1 : term39) : term41.
Proof. exact (fun h0 : term40 => @lem1363002 h1 h0). Qed.
Lemma lem1363004 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1363005 (h1 : term39) (h2 : term40) : term39.
Proof. exact (@lem1363003 h1 (@lem1363004 h2)). Qed.
Lemma lem1363006 (h1 : term40) : term40.
Proof. exact (fun h0 : term39 => @lem1363005 h0 h1). Qed.
Lemma lem1363007 : term42.
Proof. exact (fun h0 : term40 => @lem1363006 h0). Qed.
Lemma lem1363010 : term40.
Proof. exact (@lem1363007 (@lem1362999)). Qed.
Lemma lem1363032 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1363033 : term43 = term44.
Proof. exact (@lem1363032 term45). Qed.
Lemma lem1363088 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1363089 : term47 = term48.
Proof. exact (MK_COMB (@lem1363088) (@lem1363033)). Qed.
Lemma lem1363092 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1363093 : term50 = term51.
Proof. exact (MK_COMB (@lem1363092) (@lem1363089)). Qed.
Lemma lem1363096 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1363103 : term39 = term53.
Proof. exact (MK_COMB (@lem1363096) (@lem1363093)). Qed.
Lemma lem1363108 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1363109 (x : real) : (term55 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem1363108 y x)). Qed.
Lemma lem1363110 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363111 (x : real) : (term56 x) = (term56 x).
Proof. exact (MK_COMB (@lem1363110) (@lem1363109 x)). Qed.
Lemma lem1363112 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1363111 x)). Qed.
Lemma lem1363113 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363114 : term45 = term45.
Proof. exact (MK_COMB (@lem1363113) (@lem1363112)). Qed.
Lemma lem1363115 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1363116 : term44 = term44.
Proof. exact (MK_COMB (@lem1363115) (@lem1363114)). Qed.
Lemma lem1363125 (x : real) (y : real) : ((term58 y x) = (x = y)) = ((term58 y x) = (x = y)).
Proof. exact (eq_refl ((term58 y x) = (x = y))). Qed.
Lemma lem1363126 (x : real) : (term59 x) = (term59 x).
Proof. exact (fun_ext (fun y : real => @lem1363125 x y)). Qed.
Lemma lem1363127 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363128 (x : real) : (term60 x) = (term60 x).
Proof. exact (MK_COMB (@lem1363127) (@lem1363126 x)). Qed.
Lemma lem1363129 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem1363128 x)). Qed.
Lemma lem1363130 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363131 : term62 = term62.
Proof. exact (MK_COMB (@lem1363130) (@lem1363129)). Qed.
Lemma lem1363132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1363133 : term46 = term46.
Proof. exact (MK_COMB (@lem1363132) (@lem1363131)). Qed.
Lemma lem1363134 : term48 = term48.
Proof. exact (MK_COMB (@lem1363133) (@lem1363116)). Qed.
Lemma lem1363137 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1363138 : term51 = term51.
Proof. exact (MK_COMB (@lem1363137) (@lem1363134)). Qed.
Lemma lem1363142 (x : real) (h1 : (term24 x) = False) : (term24 x) = False.
Proof. exact (h1). Qed.
Lemma lem1363143 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1363144 (x : real) (h1 : (term24 x) = False) : (term26 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1363143) (@lem1363142 x h1)). Qed.
Lemma lem1363145 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1363146 (x : real) (h1 : (term24 x) = False) : (term28 x) = (term63 x).
Proof. exact (MK_COMB (@lem1363144 x h1) (@lem1363145 x)). Qed.
Lemma lem1363147 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1363148 (x : real) (h1 : (term24 x) = False) : (term29 x) = (term64 x).
Proof. exact (MK_COMB (@lem1363146 x h1) (@lem1363147 x)). Qed.
Lemma lem1363150 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1363151 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1363150 real t1 t2). Qed.
Lemma lem1363152 (x : real) : (term64 x) = x.
Proof. exact (@lem1363151 (real_neg x) x). Qed.
Lemma lem1363153 (x : real) (h1 : (term24 x) = False) : (term29 x) = x.
Proof. exact (TRANS (@lem1363148 x h1) (@lem1363152 x)). Qed.
Lemma lem1363154 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1363155 (x : real) (h1 : (term24 x) = False) : (term31 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1363154) (@lem1363153 x h1)). Qed.
Lemma lem1363156 (x : real) : (term17 x) = (term17 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1363157 (x : real) (h1 : (term24 x) = False) : ((term29 x) = (term17 x)) = (x = (term17 x)).
Proof. exact (MK_COMB (@lem1363155 x h1) (@lem1363156 x)). Qed.
Lemma lem1363160 (x : real) : term65 x.
Proof. exact (fun h0 : (term24 x) = False => @lem1363157 x h0). Qed.
Lemma lem1363162 (x : real) (h1 : (term24 x) = True) : (term24 x) = True.
Proof. exact (h1). Qed.
Lemma lem1363163 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1363164 (x : real) (h1 : (term24 x) = True) : (term26 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1363163) (@lem1363162 x h1)). Qed.
Lemma lem1363165 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1363166 (x : real) (h1 : (term24 x) = True) : (term28 x) = (term66 x).
Proof. exact (MK_COMB (@lem1363164 x h1) (@lem1363165 x)). Qed.
Lemma lem1363167 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1363168 (x : real) (h1 : (term24 x) = True) : (term29 x) = (term67 x).
Proof. exact (MK_COMB (@lem1363166 x h1) (@lem1363167 x)). Qed.
Lemma lem1363170 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1363171 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1363170 real t2 t1). Qed.
Lemma lem1363172 (x : real) : (term67 x) = (real_neg x).
Proof. exact (@lem1363171 x (real_neg x)). Qed.
Lemma lem1363173 (x : real) (h1 : (term24 x) = True) : (term29 x) = (real_neg x).
Proof. exact (TRANS (@lem1363168 x h1) (@lem1363172 x)). Qed.
Lemma lem1363174 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1363175 (x : real) (h1 : (term24 x) = True) : (term31 x) = (term68 x).
Proof. exact (MK_COMB (@lem1363174) (@lem1363173 x h1)). Qed.
Lemma lem1363176 (x : real) : (term17 x) = (term17 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1363177 (x : real) (h1 : (term24 x) = True) : ((term29 x) = (term17 x)) = ((real_neg x) = (term17 x)).
Proof. exact (MK_COMB (@lem1363175 x h1) (@lem1363176 x)). Qed.
Lemma lem1363180 (x : real) : term69 x.
Proof. exact (fun h0 : (term24 x) = True => @lem1363177 x h0). Qed.
Lemma lem1363181 (x : real) : term70 x.
Proof. exact (conj (@lem1363160 x) (@lem1363180 x)). Qed.
Lemma lem1363183 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term71 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1363184 (x : real) : term72 x.
Proof. exact (@lem1363183 ((term29 x) = (term17 x)) ((real_neg x) = (term17 x)) (term24 x) (x = (term17 x))). Qed.
Lemma lem1363199 (x : real) : ((term29 x) = (term17 x)) = (term73 x).
Proof. exact (@lem1363184 x (@lem1363181 x)). Qed.
Lemma lem1363203 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1363204 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1363205 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1363204) (@lem1363203 x h1)). Qed.
Lemma lem1363206 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1363207 (x : real) (h1 : (term74 x) = False) : (term76 x) = (@COND real False x).
Proof. exact (MK_COMB (@lem1363205 x h1) (@lem1363206 x)). Qed.
Lemma lem1363208 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1363209 (x : real) (h1 : (term74 x) = False) : (term17 x) = (term77 x).
Proof. exact (MK_COMB (@lem1363207 x h1) (@lem1363208 x)). Qed.
Lemma lem1363211 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1363212 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1363211 real t1 t2). Qed.
Lemma lem1363213 (x : real) : (term77 x) = (real_neg x).
Proof. exact (@lem1363212 x (real_neg x)). Qed.
Lemma lem1363214 (x : real) (h1 : (term74 x) = False) : (term17 x) = (real_neg x).
Proof. exact (TRANS (@lem1363209 x h1) (@lem1363213 x)). Qed.
Lemma lem1363215 (x : real) : (term68 x) = (term68 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1363216 (x : real) (h1 : (term74 x) = False) : ((real_neg x) = (term17 x)) = ((real_neg x) = (real_neg x)).
Proof. exact (MK_COMB (@lem1363215 x) (@lem1363214 x h1)). Qed.
Lemma lem1363218 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1363219 (x : real) : (x = x) = True.
Proof. exact (@lem1363218 real x). Qed.
Lemma lem1363220 (x : real) : ((real_neg x) = (real_neg x)) = True.
Proof. exact (@lem1363219 (real_neg x)). Qed.
Lemma lem1363221 (x : real) (h1 : (term74 x) = False) : ((real_neg x) = (term17 x)) = True.
Proof. exact (TRANS (@lem1363216 x h1) (@lem1363220 x)). Qed.
Lemma lem1363222 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1363223 (x : real) (h1 : (term74 x) = False) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1363222 x) (@lem1363221 x h1)). Qed.
Lemma lem1363225 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1363226 (x : real) : (term80 x) = True.
Proof. exact (@lem1363225 (term81 x)). Qed.
Lemma lem1363227 (x : real) (h1 : (term74 x) = False) : (term79 x) = True.
Proof. exact (TRANS (@lem1363223 x h1) (@lem1363226 x)). Qed.
Lemma lem1363228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363229 (x : real) (h1 : (term74 x) = False) : (term82 x) = (and True).
Proof. exact (MK_COMB (@lem1363228) (@lem1363227 x h1)). Qed.
Lemma lem1363231 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1363232 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1363233 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1363232) (@lem1363231 x h1)). Qed.
Lemma lem1363234 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1363235 (x : real) (h1 : (term74 x) = False) : (term76 x) = (@COND real False x).
Proof. exact (MK_COMB (@lem1363233 x h1) (@lem1363234 x)). Qed.
Lemma lem1363236 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1363237 (x : real) (h1 : (term74 x) = False) : (term17 x) = (term77 x).
Proof. exact (MK_COMB (@lem1363235 x h1) (@lem1363236 x)). Qed.
Lemma lem1363239 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1363240 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1363239 real t1 t2). Qed.
Lemma lem1363241 (x : real) : (term77 x) = (real_neg x).
Proof. exact (@lem1363240 x (real_neg x)). Qed.
Lemma lem1363242 (x : real) (h1 : (term74 x) = False) : (term17 x) = (real_neg x).
Proof. exact (TRANS (@lem1363237 x h1) (@lem1363241 x)). Qed.
Lemma lem1363243 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem1363244 (x : real) (h1 : (term74 x) = False) : (x = (term17 x)) = (x = (real_neg x)).
Proof. exact (MK_COMB (@lem1363243 x) (@lem1363242 x h1)). Qed.
Lemma lem1363247 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1363248 (x : real) (h1 : (term74 x) = False) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1363247 x) (@lem1363244 x h1)). Qed.
Lemma lem1363251 (x : real) (h1 : (term74 x) = False) : (term73 x) = (term86 x).
Proof. exact (MK_COMB (@lem1363229 x h1) (@lem1363248 x h1)). Qed.
Lemma lem1363253 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1363254 (x : real) : (term86 x) = (term85 x).
Proof. exact (@lem1363253 (term85 x)). Qed.
Lemma lem1363257 (x : real) (h1 : (term74 x) = False) : (term73 x) = (term85 x).
Proof. exact (TRANS (@lem1363251 x h1) (@lem1363254 x)). Qed.
Lemma lem1363258 (x : real) : term87 x.
Proof. exact (fun h0 : (term74 x) = False => @lem1363257 x h0). Qed.
Lemma lem1363260 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1363261 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1363262 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1363261) (@lem1363260 x h1)). Qed.
Lemma lem1363263 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1363264 (x : real) (h1 : (term74 x) = True) : (term76 x) = (@COND real True x).
Proof. exact (MK_COMB (@lem1363262 x h1) (@lem1363263 x)). Qed.
Lemma lem1363265 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1363266 (x : real) (h1 : (term74 x) = True) : (term17 x) = (term88 x).
Proof. exact (MK_COMB (@lem1363264 x h1) (@lem1363265 x)). Qed.
Lemma lem1363268 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1363269 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1363268 real t2 t1). Qed.
Lemma lem1363270 (x : real) : (term88 x) = x.
Proof. exact (@lem1363269 (real_neg x) x). Qed.
Lemma lem1363271 (x : real) (h1 : (term74 x) = True) : (term17 x) = x.
Proof. exact (TRANS (@lem1363266 x h1) (@lem1363270 x)). Qed.
Lemma lem1363272 (x : real) : (term68 x) = (term68 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1363273 (x : real) (h1 : (term74 x) = True) : ((real_neg x) = (term17 x)) = ((real_neg x) = x).
Proof. exact (MK_COMB (@lem1363272 x) (@lem1363271 x h1)). Qed.
Lemma lem1363276 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1363277 (x : real) (h1 : (term74 x) = True) : (term79 x) = (term89 x).
Proof. exact (MK_COMB (@lem1363276 x) (@lem1363273 x h1)). Qed.
Lemma lem1363280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363281 (x : real) (h1 : (term74 x) = True) : (term82 x) = (term90 x).
Proof. exact (MK_COMB (@lem1363280) (@lem1363277 x h1)). Qed.
Lemma lem1363283 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1363284 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1363285 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1363284) (@lem1363283 x h1)). Qed.
Lemma lem1363286 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1363287 (x : real) (h1 : (term74 x) = True) : (term76 x) = (@COND real True x).
Proof. exact (MK_COMB (@lem1363285 x h1) (@lem1363286 x)). Qed.
Lemma lem1363288 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1363289 (x : real) (h1 : (term74 x) = True) : (term17 x) = (term88 x).
Proof. exact (MK_COMB (@lem1363287 x h1) (@lem1363288 x)). Qed.
Lemma lem1363291 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1363292 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1363291 real t2 t1). Qed.
Lemma lem1363293 (x : real) : (term88 x) = x.
Proof. exact (@lem1363292 (real_neg x) x). Qed.
Lemma lem1363294 (x : real) (h1 : (term74 x) = True) : (term17 x) = x.
Proof. exact (TRANS (@lem1363289 x h1) (@lem1363293 x)). Qed.
Lemma lem1363295 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem1363296 (x : real) (h1 : (term74 x) = True) : (x = (term17 x)) = (x = x).
Proof. exact (MK_COMB (@lem1363295 x) (@lem1363294 x h1)). Qed.
Lemma lem1363298 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1363299 (x : real) : (x = x) = True.
Proof. exact (@lem1363298 real x). Qed.
Lemma lem1363300 (x : real) (h1 : (term74 x) = True) : (x = (term17 x)) = True.
Proof. exact (TRANS (@lem1363296 x h1) (@lem1363299 x)). Qed.
Lemma lem1363301 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1363302 (x : real) (h1 : (term74 x) = True) : (term84 x) = (term91 x).
Proof. exact (MK_COMB (@lem1363301 x) (@lem1363300 x h1)). Qed.
Lemma lem1363304 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1363305 (x : real) : (term91 x) = True.
Proof. exact (@lem1363304 (term24 x)). Qed.
Lemma lem1363306 (x : real) (h1 : (term74 x) = True) : (term84 x) = True.
Proof. exact (TRANS (@lem1363302 x h1) (@lem1363305 x)). Qed.
Lemma lem1363307 (x : real) (h1 : (term74 x) = True) : (term73 x) = (term92 x).
Proof. exact (MK_COMB (@lem1363281 x h1) (@lem1363306 x h1)). Qed.
Lemma lem1363309 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1363310 (x : real) : (term92 x) = (term89 x).
Proof. exact (@lem1363309 (term89 x)). Qed.
Lemma lem1363313 (x : real) (h1 : (term74 x) = True) : (term73 x) = (term89 x).
Proof. exact (TRANS (@lem1363307 x h1) (@lem1363310 x)). Qed.
Lemma lem1363314 (x : real) : term93 x.
Proof. exact (fun h0 : (term74 x) = True => @lem1363313 x h0). Qed.
Lemma lem1363315 (x : real) : term94 x.
Proof. exact (conj (@lem1363258 x) (@lem1363314 x)). Qed.
Lemma lem1363317 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term71 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1363318 (x : real) : term95 x.
Proof. exact (@lem1363317 (term73 x) (term89 x) (term74 x) (term85 x)). Qed.
Lemma lem1363361 (x : real) : (term73 x) = (term96 x).
Proof. exact (@lem1363318 x (@lem1363315 x)). Qed.
Lemma lem1363362 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1363363 (x : real) : (((term29 x) = (term17 x)) = (term73 x)) = (((term29 x) = (term17 x)) = (term96 x)).
Proof. exact (MK_COMB (@lem1363362 x) (@lem1363361 x)). Qed.
Lemma lem1363364 (x : real) : ((term29 x) = (term17 x)) = (term96 x).
Proof. exact (EQ_MP (@lem1363363 x) (@lem1363199 x)). Qed.
Lemma lem1363365 : term33 = term98.
Proof. exact (fun_ext (fun x : real => @lem1363364 x)). Qed.
Lemma lem1363366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363367 : term35 = term99.
Proof. exact (MK_COMB (@lem1363366) (@lem1363365)). Qed.
Lemma lem1363368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1363369 : term38 = term100.
Proof. exact (MK_COMB (@lem1363368) (@lem1363367)). Qed.
Lemma lem1363370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1363371 : term52 = term101.
Proof. exact (MK_COMB (@lem1363370) (@lem1363369)). Qed.
Lemma lem1363372 : term53 = term102.
Proof. exact (MK_COMB (@lem1363371) (@lem1363138)). Qed.
Lemma lem1363425 : term39 = term102.
Proof. exact (TRANS (@lem1363103) (@lem1363372)). Qed.
Lemma lem1363426 : term102 = term39.
Proof. exact (SYM (@lem1363425)). Qed.
Lemma lem1363427 (h1 : term100) : term100.
Proof. exact (h1). Qed.
Lemma lem1363429 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1363430 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1363433 (x : real) : (term103 x) = (term74 x).
Proof. exact (@lem16933 (term74 x)). Qed.
Lemma lem1363436 (x : real) : (term104 x) = (term24 x).
Proof. exact (@lem16933 (term24 x)). Qed.
Lemma lem1363437 (x : real) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1363438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363439 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1363438) (@lem1363436 x)). Qed.
Lemma lem1363440 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1363439 x) (@lem1363437 x)). Qed.
Lemma lem1363441 (x : real) : (term110 x) = (term108 x).
Proof. exact (@lem17160 (term81 x) ((real_neg x) = x)). Qed.
Lemma lem1363442 (x : real) : (term110 x) = (term109 x).
Proof. exact (TRANS (@lem1363441 x) (@lem1363440 x)). Qed.
Lemma lem1363443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363444 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1363443) (@lem1363433 x)). Qed.
Lemma lem1363445 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1363444 x) (@lem1363442 x)). Qed.
Lemma lem1363446 (x : real) : (term115 x) = (term113 x).
Proof. exact (@lem17160 (term116 x) (term89 x)). Qed.
Lemma lem1363447 (x : real) : (term115 x) = (term114 x).
Proof. exact (TRANS (@lem1363446 x) (@lem1363445 x)). Qed.
Lemma lem1363455 (x : real) : (term117 x) = (term118 x).
Proof. exact (@lem17160 (term24 x) (x = (real_neg x))). Qed.
Lemma lem1363457 (x : real) : (term119 x) = (term119 x).
Proof. exact (eq_refl (term119 x)). Qed.
Lemma lem1363458 (x : real) : (term120 x) = (term121 x).
Proof. exact (MK_COMB (@lem1363457 x) (@lem1363455 x)). Qed.
Lemma lem1363459 (x : real) : (term122 x) = (term120 x).
Proof. exact (@lem17160 (term74 x) (term85 x)). Qed.
Lemma lem1363460 (x : real) : (term122 x) = (term121 x).
Proof. exact (TRANS (@lem1363459 x) (@lem1363458 x)). Qed.
Lemma lem1363461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1363462 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1363461) (@lem1363447 x)). Qed.
Lemma lem1363463 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1363462 x) (@lem1363460 x)). Qed.
Lemma lem1363464 (x : real) : (term127 x) = (term125 x).
Proof. exact (@lem17045 (term128 x) (term129 x)). Qed.
Lemma lem1363465 (x : real) : (term127 x) = (term126 x).
Proof. exact (TRANS (@lem1363464 x) (@lem1363463 x)). Qed.
Lemma lem1363466 (P : real -> Prop) : (term130 P) = (term131 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1363467 : term100 = term132.
Proof. exact (@lem1363466 term98). Qed.
Lemma lem1363468 (x : real) : (term133 x) = (term96 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1363469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1363470 (x : real) : (term134 x) = (term127 x).
Proof. exact (MK_COMB (@lem1363469) (@lem1363468 x)). Qed.
Lemma lem1363471 (x : real) : (term134 x) = (term126 x).
Proof. exact (TRANS (@lem1363470 x) (@lem1363465 x)). Qed.
Lemma lem1363472 : term135 = term136.
Proof. exact (fun_ext (fun x : real => @lem1363471 x)). Qed.
Lemma lem1363473 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363474 : term132 = term137.
Proof. exact (MK_COMB (@lem1363473) (@lem1363472)). Qed.
Lemma lem1363475 : term100 = term137.
Proof. exact (TRANS (@lem1363467) (@lem1363474)). Qed.
Lemma lem1363477 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1363478 (P : real -> Prop) (Q : real -> Prop) : (term140 P Q) = (term141 P Q).
Proof. exact (@lem1363477 real P Q). Qed.
Lemma lem1363479 : term142 = term143.
Proof. exact (@lem1363478 term144 term145). Qed.
Lemma lem1363480 (x : real) : (term146 x) = (term114 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1363481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1363482 (x : real) : (term147 x) = (term124 x).
Proof. exact (MK_COMB (@lem1363481) (@lem1363480 x)). Qed.
Lemma lem1363483 (x : real) : (term148 x) = (term121 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1363484 (x : real) : (term149 x) = (term126 x).
Proof. exact (MK_COMB (@lem1363482 x) (@lem1363483 x)). Qed.
Lemma lem1363485 : term150 = term136.
Proof. exact (fun_ext (fun x : real => @lem1363484 x)). Qed.
Lemma lem1363486 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363487 : term142 = term137.
Proof. exact (MK_COMB (@lem1363486) (@lem1363485)). Qed.
Lemma lem1363488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1363489 : term151 = term152.
Proof. exact (MK_COMB (@lem1363488) (@lem1363487)). Qed.
Lemma lem1363490 (x : real) : (term146 x) = (term114 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1363491 : term153 = term144.
Proof. exact (fun_ext (fun x : real => @lem1363490 x)). Qed.
Lemma lem1363492 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363493 : term154 = term155.
Proof. exact (MK_COMB (@lem1363492) (@lem1363491)). Qed.
Lemma lem1363494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1363495 : term156 = term157.
Proof. exact (MK_COMB (@lem1363494) (@lem1363493)). Qed.
Lemma lem1363496 (x : real) : (term148 x) = (term121 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1363497 : term158 = term145.
Proof. exact (fun_ext (fun x : real => @lem1363496 x)). Qed.
Lemma lem1363498 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363499 : term159 = term160.
Proof. exact (MK_COMB (@lem1363498) (@lem1363497)). Qed.
Lemma lem1363500 : term143 = term161.
Proof. exact (MK_COMB (@lem1363495) (@lem1363499)). Qed.
Lemma lem1363501 : (term142 = term143) = (term137 = term161).
Proof. exact (MK_COMB (@lem1363489) (@lem1363500)). Qed.
Lemma lem1363502 : term137 = term161.
Proof. exact (EQ_MP (@lem1363501) (@lem1363479)). Qed.
Lemma lem1363600 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1363601 (P : real -> Prop) (Q : real -> Prop) : (term141 P Q) = (term140 P Q).
Proof. exact (@lem1363600 real P Q). Qed.
Lemma lem1363602 : term143 = term142.
Proof. exact (@lem1363601 term144 term145). Qed.
Lemma lem1363603 (x : real) : (term146 x) = (term114 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1363604 : term153 = term144.
Proof. exact (fun_ext (fun x : real => @lem1363603 x)). Qed.
Lemma lem1363605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363606 : term154 = term155.
Proof. exact (MK_COMB (@lem1363605) (@lem1363604)). Qed.
Lemma lem1363607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1363608 : term156 = term157.
Proof. exact (MK_COMB (@lem1363607) (@lem1363606)). Qed.
Lemma lem1363609 (x : real) : (term148 x) = (term121 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1363610 : term158 = term145.
Proof. exact (fun_ext (fun x : real => @lem1363609 x)). Qed.
Lemma lem1363611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363612 : term159 = term160.
Proof. exact (MK_COMB (@lem1363611) (@lem1363610)). Qed.
Lemma lem1363613 : term143 = term161.
Proof. exact (MK_COMB (@lem1363608) (@lem1363612)). Qed.
Lemma lem1363614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1363615 : term162 = term163.
Proof. exact (MK_COMB (@lem1363614) (@lem1363613)). Qed.
Lemma lem1363616 (x : real) : (term146 x) = (term114 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1363617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1363618 (x : real) : (term147 x) = (term124 x).
Proof. exact (MK_COMB (@lem1363617) (@lem1363616 x)). Qed.
Lemma lem1363619 (x : real) : (term148 x) = (term121 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1363620 (x : real) : (term149 x) = (term126 x).
Proof. exact (MK_COMB (@lem1363618 x) (@lem1363619 x)). Qed.
Lemma lem1363621 : term150 = term136.
Proof. exact (fun_ext (fun x : real => @lem1363620 x)). Qed.
Lemma lem1363622 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1363623 : term142 = term137.
Proof. exact (MK_COMB (@lem1363622) (@lem1363621)). Qed.
Lemma lem1363624 : (term143 = term142) = (term161 = term137).
Proof. exact (MK_COMB (@lem1363615) (@lem1363623)). Qed.
Lemma lem1363625 : term161 = term137.
Proof. exact (EQ_MP (@lem1363624) (@lem1363602)). Qed.
Lemma lem1363626 : term137 = term137.
Proof. exact (TRANS (@lem1363502) (@lem1363625)). Qed.
Lemma lem1363627 : term100 = term137.
Proof. exact (TRANS (@lem1363475) (@lem1363626)). Qed.
Lemma lem1363628 (h1 : term100) : term137.
Proof. exact (EQ_MP (@lem1363627) (@lem1363427 h1)). Qed.
Lemma lem1363634 (h1 : term164 = term22) : term164 = term22.
Proof. exact (h1). Qed.
Lemma lem1363643 (y : real) (x : real) : (term165 y x) = (term166 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem1363648 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1363649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1363650 (y : real) (x : real) : (term167 y x) = (term168 y x).
Proof. exact (MK_COMB (@lem1363649) (@lem1363643 y x)). Qed.
Lemma lem1363651 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem1363650 y x) (@lem1363648 x y)). Qed.
Lemma lem1363656 (x : real) (y : real) : (term171 x y) = (term171 x y).
Proof. exact (eq_refl (term171 x y)). Qed.
Lemma lem1363657 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1363656 x y) (@lem1363651 x y)). Qed.
Lemma lem1363658 (x : real) (y : real) : ((term58 y x) = (x = y)) = (term172 x y).
Proof. exact (@lem17784 (term58 y x) (x = y)). Qed.
Lemma lem1363659 (x : real) (y : real) : ((term58 y x) = (x = y)) = (term173 x y).
Proof. exact (TRANS (@lem1363658 x y) (@lem1363657 x y)). Qed.
Lemma lem1363660 (x : real) : (term59 x) = (term174 x).
Proof. exact (fun_ext (fun y : real => @lem1363659 x y)). Qed.
Lemma lem1363661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363662 (x : real) : (term60 x) = (term175 x).
Proof. exact (MK_COMB (@lem1363661) (@lem1363660 x)). Qed.
Lemma lem1363663 : term61 = term176.
Proof. exact (fun_ext (fun x : real => @lem1363662 x)). Qed.
Lemma lem1363664 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363665 : term62 = term177.
Proof. exact (MK_COMB (@lem1363664) (@lem1363663)). Qed.
Lemma lem1363671 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1363672 (P : real -> Prop) (Q : real -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem1363671 real P Q). Qed.
Lemma lem1363673 (x : real) : (term182 x) = (term183 x).
Proof. exact (@lem1363672 (term184 x) (term185 x)). Qed.
Lemma lem1363674 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (eq_refl (term186 x y)). Qed.
Lemma lem1363675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363676 (x : real) (y : real) : (term188 x y) = (term171 x y).
Proof. exact (MK_COMB (@lem1363675) (@lem1363674 x y)). Qed.
Lemma lem1363677 (x : real) (y : real) : (term189 x y) = (term170 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1363678 (x : real) (y : real) : (term190 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1363676 x y) (@lem1363677 x y)). Qed.
Lemma lem1363679 (x : real) : (term191 x) = (term174 x).
Proof. exact (fun_ext (fun y : real => @lem1363678 x y)). Qed.
Lemma lem1363680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363681 (x : real) : (term182 x) = (term175 x).
Proof. exact (MK_COMB (@lem1363680) (@lem1363679 x)). Qed.
Lemma lem1363682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1363683 (x : real) : (term192 x) = (term193 x).
Proof. exact (MK_COMB (@lem1363682) (@lem1363681 x)). Qed.
Lemma lem1363684 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (eq_refl (term186 x y)). Qed.
Lemma lem1363685 (x : real) : (term194 x) = (term184 x).
Proof. exact (fun_ext (fun y : real => @lem1363684 x y)). Qed.
Lemma lem1363686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363687 (x : real) : (term195 x) = (term196 x).
Proof. exact (MK_COMB (@lem1363686) (@lem1363685 x)). Qed.
Lemma lem1363688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363689 (x : real) : (term197 x) = (term198 x).
Proof. exact (MK_COMB (@lem1363688) (@lem1363687 x)). Qed.
Lemma lem1363690 (x : real) (y : real) : (term189 x y) = (term170 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1363691 (x : real) : (term199 x) = (term185 x).
Proof. exact (fun_ext (fun y : real => @lem1363690 x y)). Qed.
Lemma lem1363692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363693 (x : real) : (term200 x) = (term201 x).
Proof. exact (MK_COMB (@lem1363692) (@lem1363691 x)). Qed.
Lemma lem1363694 (x : real) : (term183 x) = (term202 x).
Proof. exact (MK_COMB (@lem1363689 x) (@lem1363693 x)). Qed.
Lemma lem1363695 (x : real) : ((term182 x) = (term183 x)) = ((term175 x) = (term202 x)).
Proof. exact (MK_COMB (@lem1363683 x) (@lem1363694 x)). Qed.
Lemma lem1363696 (x : real) : (term175 x) = (term202 x).
Proof. exact (EQ_MP (@lem1363695 x) (@lem1363673 x)). Qed.
Lemma lem1363793 : term176 = term203.
Proof. exact (fun_ext (fun x : real => @lem1363696 x)). Qed.
Lemma lem1363794 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363795 : term177 = term204.
Proof. exact (MK_COMB (@lem1363794) (@lem1363793)). Qed.
Lemma lem1363797 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1363798 (P : real -> Prop) (Q : real -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem1363797 real P Q). Qed.
Lemma lem1363799 : term205 = term206.
Proof. exact (@lem1363798 term207 term208). Qed.
Lemma lem1363800 (x : real) : (term209 x) = (term196 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1363801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363802 (x : real) : (term210 x) = (term198 x).
Proof. exact (MK_COMB (@lem1363801) (@lem1363800 x)). Qed.
Lemma lem1363803 (x : real) : (term211 x) = (term201 x).
Proof. exact (eq_refl (term211 x)). Qed.
Lemma lem1363804 (x : real) : (term212 x) = (term202 x).
Proof. exact (MK_COMB (@lem1363802 x) (@lem1363803 x)). Qed.
Lemma lem1363805 : term213 = term203.
Proof. exact (fun_ext (fun x : real => @lem1363804 x)). Qed.
Lemma lem1363806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363807 : term205 = term204.
Proof. exact (MK_COMB (@lem1363806) (@lem1363805)). Qed.
Lemma lem1363808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1363809 : term214 = term215.
Proof. exact (MK_COMB (@lem1363808) (@lem1363807)). Qed.
Lemma lem1363810 (x : real) : (term209 x) = (term196 x).
Proof. exact (eq_refl (term209 x)). Qed.
Lemma lem1363811 : term216 = term207.
Proof. exact (fun_ext (fun x : real => @lem1363810 x)). Qed.
Lemma lem1363812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363813 : term217 = term218.
Proof. exact (MK_COMB (@lem1363812) (@lem1363811)). Qed.
Lemma lem1363814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1363815 : term219 = term220.
Proof. exact (MK_COMB (@lem1363814) (@lem1363813)). Qed.
Lemma lem1363816 (x : real) : (term211 x) = (term201 x).
Proof. exact (eq_refl (term211 x)). Qed.
Lemma lem1363817 : term221 = term208.
Proof. exact (fun_ext (fun x : real => @lem1363816 x)). Qed.
Lemma lem1363818 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363819 : term222 = term223.
Proof. exact (MK_COMB (@lem1363818) (@lem1363817)). Qed.
Lemma lem1363820 : term206 = term224.
Proof. exact (MK_COMB (@lem1363815) (@lem1363819)). Qed.
Lemma lem1363821 : (term205 = term206) = (term204 = term224).
Proof. exact (MK_COMB (@lem1363809) (@lem1363820)). Qed.
Lemma lem1363822 : term204 = term224.
Proof. exact (EQ_MP (@lem1363821) (@lem1363799)). Qed.
Lemma lem1363929 : term177 = term224.
Proof. exact (TRANS (@lem1363795) (@lem1363822)). Qed.
Lemma lem1363930 : term62 = term224.
Proof. exact (TRANS (@lem1363665) (@lem1363929)). Qed.
Lemma lem1363931 (h1 : term62) : term224.
Proof. exact (EQ_MP (@lem1363930) (@lem1363429 h1)). Qed.
Lemma lem1363936 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1363937 (x : real) : (term55 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem1363936 y x)). Qed.
Lemma lem1363938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363939 (x : real) : (term56 x) = (term56 x).
Proof. exact (MK_COMB (@lem1363938) (@lem1363937 x)). Qed.
Lemma lem1363940 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1363939 x)). Qed.
Lemma lem1363941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1363998 : term45 = term45.
Proof. exact (MK_COMB (@lem1363941) (@lem1363940)). Qed.
Lemma lem1363999 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1363998) (@lem1363430 h1)). Qed.
Lemma lem1364016 (h1 : term164 = term22) : term164 = term22.
Proof. exact (h1). Qed.
Lemma lem1364041 (x : real) (y : real) : (term170 x y) = (term170 x y).
Proof. exact (eq_refl (term170 x y)). Qed.
Lemma lem1364042 (x : real) : (term185 x) = (term185 x).
Proof. exact (fun_ext (fun y : real => @lem1364041 x y)). Qed.
Lemma lem1364043 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364044 (x : real) : (term201 x) = (term201 x).
Proof. exact (MK_COMB (@lem1364043) (@lem1364042 x)). Qed.
Lemma lem1364045 : term208 = term208.
Proof. exact (fun_ext (fun x : real => @lem1364044 x)). Qed.
Lemma lem1364046 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364047 : term223 = term223.
Proof. exact (MK_COMB (@lem1364046) (@lem1364045)). Qed.
Lemma lem1364070 (x : real) (y : real) : (term187 x y) = (term187 x y).
Proof. exact (eq_refl (term187 x y)). Qed.
Lemma lem1364071 (x : real) : (term184 x) = (term184 x).
Proof. exact (fun_ext (fun y : real => @lem1364070 x y)). Qed.
Lemma lem1364072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364073 (x : real) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem1364072) (@lem1364071 x)). Qed.
Lemma lem1364074 : term207 = term207.
Proof. exact (fun_ext (fun x : real => @lem1364073 x)). Qed.
Lemma lem1364075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364076 : term218 = term218.
Proof. exact (MK_COMB (@lem1364075) (@lem1364074)). Qed.
Lemma lem1364077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1364078 : term220 = term220.
Proof. exact (MK_COMB (@lem1364077) (@lem1364076)). Qed.
Lemma lem1364079 : term224 = term224.
Proof. exact (MK_COMB (@lem1364078) (@lem1364047)). Qed.
Lemma lem1364080 (h1 : term62) : term224.
Proof. exact (EQ_MP (@lem1364079) (@lem1363931 h1)). Qed.
Lemma lem1364093 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1364094 (x : real) : (term55 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem1364093 y x)). Qed.
Lemma lem1364095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364096 (x : real) : (term56 x) = (term56 x).
Proof. exact (MK_COMB (@lem1364095) (@lem1364094 x)). Qed.
Lemma lem1364097 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1364096 x)). Qed.
Lemma lem1364098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364099 : term45 = term45.
Proof. exact (MK_COMB (@lem1364098) (@lem1364097)). Qed.
Lemma lem1364100 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1364099) (@lem1363999 h1)). Qed.
Lemma lem1364174 (x : real) (h1 : term126 x) : term126 x.
Proof. exact (h1). Qed.
Lemma lem1364175 (h1 : term62) : term223.
Proof. exact (proj2 (@lem1364080 h1)). Qed.
Lemma lem1364177 (x : real) (h1 : term114 x) : term114 x.
Proof. exact (h1). Qed.
Lemma lem1364178 (x : real) (h1 : term121 x) : term121 x.
Proof. exact (h1). Qed.
Lemma lem1364179 (x : real) (h1 : term114 x) : term109 x.
Proof. exact (proj2 (@lem1364177 x h1)). Qed.
Lemma lem1364183 (x : real) (h1 : term121 x) : term118 x.
Proof. exact (proj2 (@lem1364178 x h1)). Qed.
Lemma lem1364190 (h1 : term164 = term22) : term164 = term22.
Proof. exact (h1). Qed.
Lemma lem1364246 (x : real) (y : real) : (term170 x y) = (term170 x y).
Proof. exact (eq_refl (term170 x y)). Qed.
Lemma lem1364247 (x : real) : (term185 x) = (term185 x).
Proof. exact (fun_ext (fun y : real => @lem1364246 x y)). Qed.
Lemma lem1364248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364249 (x : real) : (term201 x) = (term201 x).
Proof. exact (MK_COMB (@lem1364248) (@lem1364247 x)). Qed.
Lemma lem1364250 : term208 = term208.
Proof. exact (fun_ext (fun x : real => @lem1364249 x)). Qed.
Lemma lem1364251 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364253 : term223 = term223.
Proof. exact (MK_COMB (@lem1364251) (@lem1364250)). Qed.
Lemma lem1364254 (h1 : term62) : term223.
Proof. exact (EQ_MP (@lem1364253) (@lem1364175 h1)). Qed.
Lemma lem1364278 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1364279 (x : real) : (term55 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem1364278 y x)). Qed.
Lemma lem1364280 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364281 (x : real) : (term56 x) = (term56 x).
Proof. exact (MK_COMB (@lem1364280) (@lem1364279 x)). Qed.
Lemma lem1364282 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1364281 x)). Qed.
Lemma lem1364283 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1364285 : term45 = term45.
Proof. exact (MK_COMB (@lem1364283) (@lem1364282)). Qed.
Lemma lem1364286 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1364285) (@lem1364100 h1)). Qed.
Lemma lem1364359 (_24232 : real) (h1 : term62) : term211 _24232.
Proof. exact (@lem1364254 h1 _24232). Qed.
Lemma lem1364360 (_24232 : real) : (term211 _24232) = (term201 _24232).
Proof. exact (eq_refl (term211 _24232)). Qed.
Lemma lem1364361 (_24232 : real) (h1 : term62) : term201 _24232.
Proof. exact (EQ_MP (@lem1364360 _24232) (@lem1364359 _24232 h1)). Qed.
Lemma lem1364362 (_24232 : real) (_24233 : real) (h1 : term62) : term189 _24232 _24233.
Proof. exact (@lem1364361 _24232 h1 _24233). Qed.
Lemma lem1364363 (_24232 : real) (_24233 : real) : (term189 _24232 _24233) = (term170 _24232 _24233).
Proof. exact (eq_refl (term189 _24232 _24233)). Qed.
Lemma lem1364364 (_24232 : real) (_24233 : real) (h1 : term62) : term170 _24232 _24233.
Proof. exact (EQ_MP (@lem1364363 _24232 _24233) (@lem1364362 _24232 _24233 h1)). Qed.
Lemma lem1364365 (_24234 : real) (h1 : term45) : term225 _24234.
Proof. exact (@lem1364286 h1 _24234). Qed.
Lemma lem1364366 (_24234 : real) : (term225 _24234) = (term56 _24234).
Proof. exact (eq_refl (term225 _24234)). Qed.
Lemma lem1364367 (_24234 : real) (h1 : term45) : term56 _24234.
Proof. exact (EQ_MP (@lem1364366 _24234) (@lem1364365 _24234 h1)). Qed.
Lemma lem1364368 (_24234 : real) (_24235 : real) (h1 : term45) : term226 _24234 _24235.
Proof. exact (@lem1364367 _24234 h1 _24235). Qed.
Lemma lem1364369 (_24235 : real) (_24234 : real) : (term226 _24234 _24235) = (term54 _24235 _24234).
Proof. exact (eq_refl (term226 _24234 _24235)). Qed.
Lemma lem1364388 (h1 : term164 = term22) : term164 = term22.
Proof. exact (h1). Qed.
Lemma lem1364405 (_24232 : real) (_24233 : real) : (term170 _24232 _24233) = (term227 _24232 _24233).
Proof. exact (@lem1362933 (term228 _24232 _24233) (term228 _24233 _24232) (_24232 = _24233)). Qed.
Lemma lem1364406 (_24232 : real) (_24233 : real) (h1 : term62) : term227 _24232 _24233.
Proof. exact (EQ_MP (@lem1364405 _24232 _24233) (@lem1364364 _24232 _24233 h1)). Qed.
Lemma lem1364412 (x : real) (h1 : term114 x) : term105 x.
Proof. exact (proj2 (@lem1364179 x h1)). Qed.
Lemma lem1364432 (_24235 : real) (_24234 : real) (h1 : term45) : term54 _24235 _24234.
Proof. exact (EQ_MP (@lem1364369 _24235 _24234) (@lem1364368 _24234 _24235 h1)). Qed.
Lemma lem1364448 (x : real) (h1 : term121 x) : term81 x.
Proof. exact (proj1 (@lem1364183 x h1)). Qed.
Lemma lem1364482 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1364483 (_24244 : real) (_24245 : real) (h1 : _24244 = _24245) : _24244 = _24245.
Proof. exact (h1). Qed.
Lemma lem1364484 (_24244 : real) (_24245 : real) (h1 : _24244 = _24245) : (real_neg _24244) = (real_neg _24245).
Proof. exact (MK_COMB (@lem1364482) (@lem1364483 _24244 _24245 h1)). Qed.
Lemma lem1364485 (_24244 : real) (_24245 : real) : term229 _24244 _24245.
Proof. exact (fun h0 : _24244 = _24245 => @lem1364484 _24244 _24245 h0). Qed.
Lemma lem1364487 (a : Prop) (b : Prop) : (a -> b) = (term230 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1364488 (_24244 : real) (_24245 : real) : (term229 _24244 _24245) = (term231 _24244 _24245).
Proof. exact (@lem1364487 (_24244 = _24245) ((real_neg _24244) = (real_neg _24245))). Qed.
Lemma lem1364489 (_24244 : real) (_24245 : real) : term231 _24244 _24245.
Proof. exact (EQ_MP (@lem1364488 _24244 _24245) (@lem1364485 _24244 _24245)). Qed.
Lemma lem1364507 (x : real) (y : real) (z : real) : term232 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1364511 (h1 : term164 = term22) : term164 = term22.
Proof. exact (h1). Qed.
Lemma lem1364512 (h1 : term164 = term22) : term233.
Proof. exact (fun h0 : term234 => @lem1364511 h1). Qed.
Lemma lem1364514 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364515 : term233 = (term164 = term22).
Proof. exact (@lem1364514 (term164 = term22)). Qed.
Lemma lem1364516 (h1 : term164 = term22) : term164 = term22.
Proof. exact (EQ_MP (@lem1364515) (@lem1364512 h1)). Qed.
Lemma lem1364518 (x : real) (h1 : term114 x) : term74 x.
Proof. exact (proj1 (@lem1364177 x h1)). Qed.
Lemma lem1364519 (x : real) (h1 : term114 x) : term236 x.
Proof. exact (fun h0 : term116 x => @lem1364518 x h1). Qed.
Lemma lem1364521 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364522 (x : real) : (term236 x) = (term74 x).
Proof. exact (@lem1364521 (term74 x)). Qed.
Lemma lem1364523 (x : real) (h1 : term114 x) : term74 x.
Proof. exact (EQ_MP (@lem1364522 x) (@lem1364519 x h1)). Qed.
Lemma lem1364525 (x : real) (h1 : term114 x) : term24 x.
Proof. exact (proj1 (@lem1364179 x h1)). Qed.
Lemma lem1364526 (x : real) (h1 : term114 x) : term237 x.
Proof. exact (fun h0 : term81 x => @lem1364525 x h1). Qed.
Lemma lem1364528 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364529 (x : real) : (term237 x) = (term24 x).
Proof. exact (@lem1364528 (term24 x)). Qed.
Lemma lem1364530 (x : real) (h1 : term114 x) : term24 x.
Proof. exact (EQ_MP (@lem1364529 x) (@lem1364526 x h1)). Qed.
Lemma lem1364546 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1364547 (_24233 : real) (_24232 : real) : (term238 _24232 _24233) = (term239 _24233 _24232).
Proof. exact (@lem1364546 (_24232 = _24233) (term228 _24233 _24232)). Qed.
Lemma lem1364555 (_24232 : real) (_24233 : real) : (term240 _24232 _24233) = (term240 _24232 _24233).
Proof. exact (eq_refl (term240 _24232 _24233)). Qed.
Lemma lem1364556 (_24233 : real) (_24232 : real) : (term227 _24232 _24233) = (term241 _24233 _24232).
Proof. exact (MK_COMB (@lem1364555 _24232 _24233) (@lem1364547 _24233 _24232)). Qed.
Lemma lem1364560 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1364561 (_24233 : real) (_24232 : real) : (term241 _24233 _24232) = (term242 _24233 _24232).
Proof. exact (@lem1364560 (_24232 = _24233) (term228 _24232 _24233) (term228 _24233 _24232)). Qed.
Lemma lem1364579 (_24233 : real) (_24232 : real) : (term227 _24232 _24233) = (term242 _24233 _24232).
Proof. exact (TRANS (@lem1364556 _24233 _24232) (@lem1364561 _24233 _24232)). Qed.
Lemma lem1364580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1364581 (_24233 : real) (_24232 : real) : (term243 _24232 _24233) = (term244 _24233 _24232).
Proof. exact (MK_COMB (@lem1364580) (@lem1364579 _24233 _24232)). Qed.
Lemma lem1364599 (_24233 : real) (_24232 : real) : (term242 _24233 _24232) = (term242 _24233 _24232).
Proof. exact (eq_refl (term242 _24233 _24232)). Qed.
Lemma lem1364600 (_24233 : real) (_24232 : real) : ((term227 _24232 _24233) = (term242 _24233 _24232)) = ((term242 _24233 _24232) = (term242 _24233 _24232)).
Proof. exact (MK_COMB (@lem1364581 _24233 _24232) (@lem1364599 _24233 _24232)). Qed.
Lemma lem1364602 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1364603 (x : Prop) : (x = x) = True.
Proof. exact (@lem1364602 Prop x). Qed.
Lemma lem1364604 (_24233 : real) (_24232 : real) : ((term242 _24233 _24232) = (term242 _24233 _24232)) = True.
Proof. exact (@lem1364603 (term242 _24233 _24232)). Qed.
Lemma lem1364605 (_24233 : real) (_24232 : real) : ((term227 _24232 _24233) = (term242 _24233 _24232)) = True.
Proof. exact (TRANS (@lem1364600 _24233 _24232) (@lem1364604 _24233 _24232)). Qed.
Lemma lem1364606 (_24233 : real) (_24232 : real) : True = ((term227 _24232 _24233) = (term242 _24233 _24232)).
Proof. exact (SYM (@lem1364605 _24233 _24232)). Qed.
Lemma lem1364607 (_24233 : real) (_24232 : real) : (term227 _24232 _24233) = (term242 _24233 _24232).
Proof. exact (EQ_MP (@lem1364606 _24233 _24232) (@lem0)). Qed.
Lemma lem1364608 (_24233 : real) (_24232 : real) (h1 : term62) : term242 _24233 _24232.
Proof. exact (EQ_MP (@lem1364607 _24233 _24232) (@lem1364406 _24232 _24233 h1)). Qed.
Lemma lem1364610 (b : Prop) (a : Prop) : (a \/ b) = (term245 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1364611 (_24232 : real) (_24233 : real) : (term242 _24233 _24232) = (term246 _24232 _24233).
Proof. exact (@lem1364610 (term166 _24233 _24232) (_24232 = _24233)). Qed.
Lemma lem1364613 (a : Prop) (b : Prop) : (term247 a b) = (term248 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1364614 (_24233 : real) (_24232 : real) : (term249 _24233 _24232) = (term250 _24233 _24232).
Proof. exact (@lem1364613 (term228 _24232 _24233) (term228 _24233 _24232)). Qed.
Lemma lem1364616 (a : Prop) : (term251 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1364617 (_24232 : real) (_24233 : real) : (term252 _24232 _24233) = (real_le _24232 _24233).
Proof. exact (@lem1364616 (real_le _24232 _24233)). Qed.
Lemma lem1364618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1364619 (_24232 : real) (_24233 : real) : (term253 _24232 _24233) = (term254 _24232 _24233).
Proof. exact (MK_COMB (@lem1364618) (@lem1364617 _24232 _24233)). Qed.
Lemma lem1364621 (a : Prop) : (term251 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1364622 (_24233 : real) (_24232 : real) : (term252 _24233 _24232) = (real_le _24233 _24232).
Proof. exact (@lem1364621 (real_le _24233 _24232)). Qed.
Lemma lem1364623 (_24233 : real) (_24232 : real) : (term250 _24233 _24232) = (term58 _24233 _24232).
Proof. exact (MK_COMB (@lem1364619 _24232 _24233) (@lem1364622 _24233 _24232)). Qed.
Lemma lem1364624 (_24233 : real) (_24232 : real) : (term249 _24233 _24232) = (term58 _24233 _24232).
Proof. exact (TRANS (@lem1364614 _24233 _24232) (@lem1364623 _24233 _24232)). Qed.
Lemma lem1364625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1364626 (_24233 : real) (_24232 : real) : (term255 _24233 _24232) = (term256 _24233 _24232).
Proof. exact (MK_COMB (@lem1364625) (@lem1364624 _24233 _24232)). Qed.
Lemma lem1364627 (_24232 : real) (_24233 : real) : (_24232 = _24233) = (_24232 = _24233).
Proof. exact (eq_refl (_24232 = _24233)). Qed.
Lemma lem1364628 (_24232 : real) (_24233 : real) : (term246 _24232 _24233) = (term257 _24232 _24233).
Proof. exact (MK_COMB (@lem1364626 _24233 _24232) (@lem1364627 _24232 _24233)). Qed.
Lemma lem1364629 (_24232 : real) (_24233 : real) : (term242 _24233 _24232) = (term257 _24232 _24233).
Proof. exact (TRANS (@lem1364611 _24232 _24233) (@lem1364628 _24232 _24233)). Qed.
Lemma lem1364631 (x : real) (h1 : term114 x) : term258 x.
Proof. exact (conj (@lem1364523 x h1) (@lem1364530 x h1)). Qed.
Lemma lem1364633 (_24232 : real) (_24233 : real) (h1 : term62) : term257 _24232 _24233.
Proof. exact (EQ_MP (@lem1364629 _24232 _24233) (@lem1364608 _24233 _24232 h1)). Qed.
Lemma lem1364634 (x : real) (h1 : term62) : term259 x.
Proof. exact (@lem1364633 term22 x h1). Qed.
Lemma lem1364637 (x : real) (h1 : term62) (h2 : term114 x) : term22 = x.
Proof. exact (@lem1364634 x h1 (@lem1364631 x h2)). Qed.
Lemma lem1364638 (x : real) (h1 : term62) (h2 : term114 x) : term260 x.
Proof. exact (fun h0 : term261 x => @lem1364637 x h1 h2). Qed.
Lemma lem1364640 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364641 (x : real) : (term260 x) = (term22 = x).
Proof. exact (@lem1364640 (term22 = x)). Qed.
Lemma lem1364642 (x : real) (h1 : term62) (h2 : term114 x) : term22 = x.
Proof. exact (EQ_MP (@lem1364641 x) (@lem1364638 x h1 h2)). Qed.
Lemma lem1364648 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1364649 (_24244 : real) (_24245 : real) : (term231 _24244 _24245) = (term262 _24244 _24245).
Proof. exact (@lem1364648 ((real_neg _24244) = (real_neg _24245)) (term263 _24244 _24245)). Qed.
Lemma lem1364659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1364660 (_24244 : real) (_24245 : real) : (term264 _24244 _24245) = (term265 _24244 _24245).
Proof. exact (MK_COMB (@lem1364659) (@lem1364649 _24244 _24245)). Qed.
Lemma lem1364670 (_24244 : real) (_24245 : real) : (term262 _24244 _24245) = (term262 _24244 _24245).
Proof. exact (eq_refl (term262 _24244 _24245)). Qed.
Lemma lem1364671 (_24244 : real) (_24245 : real) : ((term231 _24244 _24245) = (term262 _24244 _24245)) = ((term262 _24244 _24245) = (term262 _24244 _24245)).
Proof. exact (MK_COMB (@lem1364660 _24244 _24245) (@lem1364670 _24244 _24245)). Qed.
Lemma lem1364673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1364674 (x : Prop) : (x = x) = True.
Proof. exact (@lem1364673 Prop x). Qed.
Lemma lem1364675 (_24244 : real) (_24245 : real) : ((term262 _24244 _24245) = (term262 _24244 _24245)) = True.
Proof. exact (@lem1364674 (term262 _24244 _24245)). Qed.
Lemma lem1364676 (_24244 : real) (_24245 : real) : ((term231 _24244 _24245) = (term262 _24244 _24245)) = True.
Proof. exact (TRANS (@lem1364671 _24244 _24245) (@lem1364675 _24244 _24245)). Qed.
Lemma lem1364677 (_24244 : real) (_24245 : real) : True = ((term231 _24244 _24245) = (term262 _24244 _24245)).
Proof. exact (SYM (@lem1364676 _24244 _24245)). Qed.
Lemma lem1364678 (_24244 : real) (_24245 : real) : (term231 _24244 _24245) = (term262 _24244 _24245).
Proof. exact (EQ_MP (@lem1364677 _24244 _24245) (@lem0)). Qed.
Lemma lem1364679 (_24244 : real) (_24245 : real) : term262 _24244 _24245.
Proof. exact (EQ_MP (@lem1364678 _24244 _24245) (@lem1364489 _24244 _24245)). Qed.
Lemma lem1364681 (b : Prop) (a : Prop) : (a \/ b) = (term245 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1364682 (_24244 : real) (_24245 : real) : (term262 _24244 _24245) = (term266 _24244 _24245).
Proof. exact (@lem1364681 (term263 _24244 _24245) ((real_neg _24244) = (real_neg _24245))). Qed.
Lemma lem1364684 (a : Prop) : (term251 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1364685 (_24244 : real) (_24245 : real) : (term267 _24244 _24245) = (_24244 = _24245).
Proof. exact (@lem1364684 (_24244 = _24245)). Qed.
Lemma lem1364686 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1364687 (_24244 : real) (_24245 : real) : (term268 _24244 _24245) = (term269 _24244 _24245).
Proof. exact (MK_COMB (@lem1364686) (@lem1364685 _24244 _24245)). Qed.
Lemma lem1364688 (_24244 : real) (_24245 : real) : ((real_neg _24244) = (real_neg _24245)) = ((real_neg _24244) = (real_neg _24245)).
Proof. exact (eq_refl ((real_neg _24244) = (real_neg _24245))). Qed.
Lemma lem1364689 (_24244 : real) (_24245 : real) : (term266 _24244 _24245) = (term229 _24244 _24245).
Proof. exact (MK_COMB (@lem1364687 _24244 _24245) (@lem1364688 _24244 _24245)). Qed.
Lemma lem1364690 (_24244 : real) (_24245 : real) : (term262 _24244 _24245) = (term229 _24244 _24245).
Proof. exact (TRANS (@lem1364682 _24244 _24245) (@lem1364689 _24244 _24245)). Qed.
Lemma lem1364693 (_24244 : real) (_24245 : real) : term229 _24244 _24245.
Proof. exact (EQ_MP (@lem1364690 _24244 _24245) (@lem1364679 _24244 _24245)). Qed.
Lemma lem1364694 (x : real) : term270 x.
Proof. exact (@lem1364693 term22 x). Qed.
Lemma lem1364697 (x : real) (h1 : term62) (h2 : term114 x) : term164 = (real_neg x).
Proof. exact (@lem1364694 x (@lem1364642 x h1 h2)). Qed.
Lemma lem1364698 (x : real) (h1 : term62) (h2 : term114 x) : term271 x.
Proof. exact (fun h0 : term272 x => @lem1364697 x h1 h2). Qed.
Lemma lem1364700 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364701 (x : real) : (term271 x) = (term164 = (real_neg x)).
Proof. exact (@lem1364700 (term164 = (real_neg x))). Qed.
Lemma lem1364702 (x : real) (h1 : term62) (h2 : term114 x) : term164 = (real_neg x).
Proof. exact (EQ_MP (@lem1364701 x) (@lem1364698 x h1 h2)). Qed.
Lemma lem1364720 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1364721 (y : real) (x : real) (z : real) : (term273 x y z) = (term274 y x z).
Proof. exact (@lem1364720 (y = z) (term263 x z)). Qed.
Lemma lem1364731 (x : real) (y : real) : (term275 x y) = (term275 x y).
Proof. exact (eq_refl (term275 x y)). Qed.
Lemma lem1364732 (y : real) (x : real) (z : real) : (term232 x y z) = (term276 y x z).
Proof. exact (MK_COMB (@lem1364731 x y) (@lem1364721 y x z)). Qed.
Lemma lem1364736 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1364737 (y : real) (x : real) (z : real) : (term276 y x z) = (term277 y x z).
Proof. exact (@lem1364736 (y = z) (term263 x y) (term263 x z)). Qed.
Lemma lem1364759 (y : real) (x : real) (z : real) : (term232 x y z) = (term277 y x z).
Proof. exact (TRANS (@lem1364732 y x z) (@lem1364737 y x z)). Qed.
Lemma lem1364760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1364761 (y : real) (x : real) (z : real) : (term278 x y z) = (term279 y x z).
Proof. exact (MK_COMB (@lem1364760) (@lem1364759 y x z)). Qed.
Lemma lem1364783 (y : real) (x : real) (z : real) : (term277 y x z) = (term277 y x z).
Proof. exact (eq_refl (term277 y x z)). Qed.
Lemma lem1364784 (y : real) (x : real) (z : real) : ((term232 x y z) = (term277 y x z)) = ((term277 y x z) = (term277 y x z)).
Proof. exact (MK_COMB (@lem1364761 y x z) (@lem1364783 y x z)). Qed.
Lemma lem1364786 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1364787 (x : Prop) : (x = x) = True.
Proof. exact (@lem1364786 Prop x). Qed.
Lemma lem1364788 (y : real) (x : real) (z : real) : ((term277 y x z) = (term277 y x z)) = True.
Proof. exact (@lem1364787 (term277 y x z)). Qed.
Lemma lem1364789 (y : real) (x : real) (z : real) : ((term232 x y z) = (term277 y x z)) = True.
Proof. exact (TRANS (@lem1364784 y x z) (@lem1364788 y x z)). Qed.
Lemma lem1364790 (y : real) (x : real) (z : real) : True = ((term232 x y z) = (term277 y x z)).
Proof. exact (SYM (@lem1364789 y x z)). Qed.
Lemma lem1364791 (y : real) (x : real) (z : real) : (term232 x y z) = (term277 y x z).
Proof. exact (EQ_MP (@lem1364790 y x z) (@lem0)). Qed.
Lemma lem1364792 (y : real) (x : real) (z : real) : term277 y x z.
Proof. exact (EQ_MP (@lem1364791 y x z) (@lem1364507 x y z)). Qed.
Lemma lem1364794 (b : Prop) (a : Prop) : (a \/ b) = (term245 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1364795 (x : real) (y : real) (z : real) : (term277 y x z) = (term280 x y z).
Proof. exact (@lem1364794 (term281 y x z) (y = z)). Qed.
Lemma lem1364797 (a : Prop) (b : Prop) : (term247 a b) = (term248 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1364798 (y : real) (x : real) (z : real) : (term282 y x z) = (term283 y x z).
Proof. exact (@lem1364797 (term263 x y) (term263 x z)). Qed.
Lemma lem1364800 (a : Prop) : (term251 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1364801 (x : real) (y : real) : (term267 x y) = (x = y).
Proof. exact (@lem1364800 (x = y)). Qed.
Lemma lem1364802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1364803 (x : real) (y : real) : (term284 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem1364802) (@lem1364801 x y)). Qed.
Lemma lem1364805 (a : Prop) : (term251 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1364806 (x : real) (z : real) : (term267 x z) = (x = z).
Proof. exact (@lem1364805 (x = z)). Qed.
Lemma lem1364807 (y : real) (x : real) (z : real) : (term283 y x z) = (term286 y x z).
Proof. exact (MK_COMB (@lem1364803 x y) (@lem1364806 x z)). Qed.
Lemma lem1364808 (y : real) (x : real) (z : real) : (term282 y x z) = (term286 y x z).
Proof. exact (TRANS (@lem1364798 y x z) (@lem1364807 y x z)). Qed.
Lemma lem1364809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1364810 (y : real) (x : real) (z : real) : (term287 y x z) = (term288 y x z).
Proof. exact (MK_COMB (@lem1364809) (@lem1364808 y x z)). Qed.
Lemma lem1364811 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1364812 (x : real) (y : real) (z : real) : (term280 x y z) = (term289 x y z).
Proof. exact (MK_COMB (@lem1364810 y x z) (@lem1364811 y z)). Qed.
Lemma lem1364813 (x : real) (y : real) (z : real) : (term277 y x z) = (term289 x y z).
Proof. exact (TRANS (@lem1364795 x y z) (@lem1364812 x y z)). Qed.
Lemma lem1364815 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term290 x.
Proof. exact (conj (@lem1364516 h3) (@lem1364702 x h1 h2)). Qed.
Lemma lem1364817 (x : real) (y : real) (z : real) : term289 x y z.
Proof. exact (EQ_MP (@lem1364813 x y z) (@lem1364792 y x z)). Qed.
Lemma lem1364818 (x : real) : term291 x.
Proof. exact (@lem1364817 term164 term22 (real_neg x)). Qed.
Lemma lem1364821 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term22 = (real_neg x).
Proof. exact (@lem1364818 x (@lem1364815 x h1 h2 h3)). Qed.
Lemma lem1364822 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term292 x.
Proof. exact (fun h0 : term293 x => @lem1364821 x h1 h2 h3). Qed.
Lemma lem1364824 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364825 (x : real) : (term292 x) = (term22 = (real_neg x)).
Proof. exact (@lem1364824 (term22 = (real_neg x))). Qed.
Lemma lem1364826 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term22 = (real_neg x).
Proof. exact (EQ_MP (@lem1364825 x) (@lem1364822 x h1 h2 h3)). Qed.
Lemma lem1364828 (x : real) (h1 : term114 x) : term74 x.
Proof. exact (proj1 (@lem1364177 x h1)). Qed.
Lemma lem1364829 (x : real) (h1 : term114 x) : term236 x.
Proof. exact (fun h0 : term116 x => @lem1364828 x h1). Qed.
Lemma lem1364831 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364832 (x : real) : (term236 x) = (term74 x).
Proof. exact (@lem1364831 (term74 x)). Qed.
Lemma lem1364833 (x : real) (h1 : term114 x) : term74 x.
Proof. exact (EQ_MP (@lem1364832 x) (@lem1364829 x h1)). Qed.
Lemma lem1364835 (x : real) (h1 : term114 x) : term24 x.
Proof. exact (proj1 (@lem1364179 x h1)). Qed.
Lemma lem1364836 (x : real) (h1 : term114 x) : term237 x.
Proof. exact (fun h0 : term81 x => @lem1364835 x h1). Qed.
Lemma lem1364838 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364839 (x : real) : (term237 x) = (term24 x).
Proof. exact (@lem1364838 (term24 x)). Qed.
Lemma lem1364840 (x : real) (h1 : term114 x) : term24 x.
Proof. exact (EQ_MP (@lem1364839 x) (@lem1364836 x h1)). Qed.
Lemma lem1364841 (x : real) (h1 : term114 x) : term258 x.
Proof. exact (conj (@lem1364833 x h1) (@lem1364840 x h1)). Qed.
Lemma lem1364843 (_24232 : real) (_24233 : real) (h1 : term62) : term257 _24232 _24233.
Proof. exact (EQ_MP (@lem1364629 _24232 _24233) (@lem1364608 _24233 _24232 h1)). Qed.
Lemma lem1364844 (x : real) (h1 : term62) : term259 x.
Proof. exact (@lem1364843 term22 x h1). Qed.
Lemma lem1364847 (x : real) (h1 : term62) (h2 : term114 x) : term22 = x.
Proof. exact (@lem1364844 x h1 (@lem1364841 x h2)). Qed.
Lemma lem1364848 (x : real) (h1 : term62) (h2 : term114 x) : term260 x.
Proof. exact (fun h0 : term261 x => @lem1364847 x h1 h2). Qed.
Lemma lem1364850 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364851 (x : real) : (term260 x) = (term22 = x).
Proof. exact (@lem1364850 (term22 = x)). Qed.
Lemma lem1364852 (x : real) (h1 : term62) (h2 : term114 x) : term22 = x.
Proof. exact (EQ_MP (@lem1364851 x) (@lem1364848 x h1 h2)). Qed.
Lemma lem1364853 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term294 x.
Proof. exact (conj (@lem1364826 x h1 h2 h3) (@lem1364852 x h1 h2)). Qed.
Lemma lem1364855 (x : real) (y : real) (z : real) : term289 x y z.
Proof. exact (EQ_MP (@lem1364813 x y z) (@lem1364792 y x z)). Qed.
Lemma lem1364856 (x : real) : term295 x.
Proof. exact (@lem1364855 term22 (real_neg x) x). Qed.
Lemma lem1364859 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : (real_neg x) = x.
Proof. exact (@lem1364856 x (@lem1364853 x h1 h2 h3)). Qed.
Lemma lem1364860 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term296 x.
Proof. exact (fun h0 : term105 x => @lem1364859 x h1 h2 h3). Qed.
Lemma lem1364862 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364863 (x : real) : (term296 x) = ((real_neg x) = x).
Proof. exact (@lem1364862 ((real_neg x) = x)). Qed.
Lemma lem1364864 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : (real_neg x) = x.
Proof. exact (EQ_MP (@lem1364863 x) (@lem1364860 x h1 h2 h3)). Qed.
Lemma lem1364867 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1364869 (x : real) : (term105 x) = (term297 x).
Proof. exact (@lem1364867 ((real_neg x) = x)). Qed.
Lemma lem1364872 (x : real) (h1 : term114 x) : term297 x.
Proof. exact (EQ_MP (@lem1364869 x) (@lem1364412 x h1)). Qed.
Lemma lem1364875 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : False.
Proof. exact (@lem1364872 x h2 (@lem1364864 x h1 h2 h3)). Qed.
Lemma lem1364876 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : term298.
Proof. exact (fun h0 : ~ False => @lem1364875 x h1 h2 h3). Qed.
Lemma lem1364878 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364879 : term298 = False.
Proof. exact (@lem1364878 False). Qed.
Lemma lem1364880 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : False.
Proof. exact (EQ_MP (@lem1364879) (@lem1364876 x h1 h2 h3)). Qed.
Lemma lem1364929 (x : real) (h1 : term121 x) : term116 x.
Proof. exact (proj1 (@lem1364178 x h1)). Qed.
Lemma lem1364930 (x : real) (h1 : term121 x) : term299 x.
Proof. exact (fun h0 : term74 x => @lem1364929 x h1). Qed.
Lemma lem1364932 (p : Prop) : (term300 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1364933 (x : real) : (term299 x) = (term116 x).
Proof. exact (@lem1364932 (term74 x)). Qed.
Lemma lem1364934 (x : real) (h1 : term121 x) : term116 x.
Proof. exact (EQ_MP (@lem1364933 x) (@lem1364930 x h1)). Qed.
Lemma lem1364945 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1364946 (_24235 : real) (_24234 : real) : (term54 _24234 _24235) = (term54 _24235 _24234).
Proof. exact (@lem1364945 (real_le _24234 _24235) (real_le _24235 _24234)). Qed.
Lemma lem1364952 (_24235 : real) (_24234 : real) : (term301 _24235 _24234) = (term301 _24235 _24234).
Proof. exact (eq_refl (term301 _24235 _24234)). Qed.
Lemma lem1364953 (_24235 : real) (_24234 : real) : ((term54 _24235 _24234) = (term54 _24234 _24235)) = ((term54 _24235 _24234) = (term54 _24235 _24234)).
Proof. exact (MK_COMB (@lem1364952 _24235 _24234) (@lem1364946 _24235 _24234)). Qed.
Lemma lem1364955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1364956 (x : Prop) : (x = x) = True.
Proof. exact (@lem1364955 Prop x). Qed.
Lemma lem1364957 (_24235 : real) (_24234 : real) : ((term54 _24235 _24234) = (term54 _24235 _24234)) = True.
Proof. exact (@lem1364956 (term54 _24235 _24234)). Qed.
Lemma lem1364958 (_24234 : real) (_24235 : real) : ((term54 _24235 _24234) = (term54 _24234 _24235)) = True.
Proof. exact (TRANS (@lem1364953 _24235 _24234) (@lem1364957 _24235 _24234)). Qed.
Lemma lem1364959 (_24234 : real) (_24235 : real) : True = ((term54 _24235 _24234) = (term54 _24234 _24235)).
Proof. exact (SYM (@lem1364958 _24234 _24235)). Qed.
Lemma lem1364960 (_24234 : real) (_24235 : real) : (term54 _24235 _24234) = (term54 _24234 _24235).
Proof. exact (EQ_MP (@lem1364959 _24234 _24235) (@lem0)). Qed.
Lemma lem1364961 (_24234 : real) (_24235 : real) (h1 : term45) : term54 _24234 _24235.
Proof. exact (EQ_MP (@lem1364960 _24234 _24235) (@lem1364432 _24235 _24234 h1)). Qed.
Lemma lem1364963 (b : Prop) (a : Prop) : (a \/ b) = (term245 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1364966 (_24235 : real) (_24234 : real) : (term54 _24234 _24235) = (term302 _24235 _24234).
Proof. exact (@lem1364963 (real_le _24234 _24235) (real_le _24235 _24234)). Qed.
Lemma lem1364969 (_24235 : real) (_24234 : real) (h1 : term45) : term302 _24235 _24234.
Proof. exact (EQ_MP (@lem1364966 _24235 _24234) (@lem1364961 _24234 _24235 h1)). Qed.
Lemma lem1364970 (x : real) (h1 : term45) : term303 x.
Proof. exact (@lem1364969 x term22 h1). Qed.
Lemma lem1364973 (x : real) (h1 : term45) (h2 : term121 x) : term24 x.
Proof. exact (@lem1364970 x h1 (@lem1364934 x h2)). Qed.
Lemma lem1364974 (x : real) (h1 : term45) (h2 : term121 x) : term237 x.
Proof. exact (fun h0 : term81 x => @lem1364973 x h1 h2). Qed.
Lemma lem1364976 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364977 (x : real) : (term237 x) = (term24 x).
Proof. exact (@lem1364976 (term24 x)). Qed.
Lemma lem1364978 (x : real) (h1 : term45) (h2 : term121 x) : term24 x.
Proof. exact (EQ_MP (@lem1364977 x) (@lem1364974 x h1 h2)). Qed.
Lemma lem1364981 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1364983 (x : real) : (term81 x) = (term304 x).
Proof. exact (@lem1364981 (term24 x)). Qed.
Lemma lem1364986 (x : real) (h1 : term121 x) : term304 x.
Proof. exact (EQ_MP (@lem1364983 x) (@lem1364448 x h1)). Qed.
Lemma lem1364989 (x : real) (h1 : term45) (h2 : term121 x) : False.
Proof. exact (@lem1364986 x h2 (@lem1364978 x h1 h2)). Qed.
Lemma lem1364990 (x : real) (h1 : term45) (h2 : term121 x) : term298.
Proof. exact (fun h0 : ~ False => @lem1364989 x h1 h2). Qed.
Lemma lem1364992 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1364993 : term298 = False.
Proof. exact (@lem1364992 False). Qed.
Lemma lem1364994 (x : real) (h1 : term45) (h2 : term121 x) : False.
Proof. exact (EQ_MP (@lem1364993) (@lem1364990 x h1 h2)). Qed.
Lemma lem1364995 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : (term164 = term22) = False.
Proof. exact (prop_ext (fun h4 : term164 = term22 => @lem1364880 x h1 h2 h3) (fun h4 : False => @lem1364388 h3)). Qed.
Lemma lem1364996 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : False.
Proof. exact (EQ_MP (@lem1364995 x h1 h2 h3) (@lem1364388 h3)). Qed.
Lemma lem1364997 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : (term164 = term22) = False.
Proof. exact (prop_ext (fun h4 : term164 = term22 => @lem1364996 x h1 h2 h3) (fun h4 : False => @lem1364190 h3)). Qed.
Lemma lem1364998 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : False.
Proof. exact (EQ_MP (@lem1364997 x h1 h2 h3) (@lem1364190 h3)). Qed.
Lemma lem1364999 (x : real) (h1 : term45) (h2 : term121 x) : term45 = False.
Proof. exact (prop_ext (fun h3 : term45 => @lem1364994 x h1 h2) (fun h3 : False => @lem1364286 h1)). Qed.
Lemma lem1365000 (x : real) (h1 : term45) (h2 : term121 x) : False.
Proof. exact (EQ_MP (@lem1364999 x h1 h2) (@lem1364286 h1)). Qed.
Lemma lem1365001 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : (term164 = term22) = False.
Proof. exact (prop_ext (fun h4 : term164 = term22 => @lem1364998 x h1 h2 h3) (fun h4 : False => @lem1364190 h3)). Qed.
Lemma lem1365002 (x : real) (h1 : term62) (h2 : term114 x) (h3 : term164 = term22) : False.
Proof. exact (EQ_MP (@lem1365001 x h1 h2 h3) (@lem1364190 h3)). Qed.
Lemma lem1365003 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : False.
Proof. exact (or_elim (@lem1364174 x h4) (fun h0 : term114 x => @lem1365002 x h1 h0 h3) (fun h0 : term121 x => @lem1365000 x h2 h0)). Qed.
Lemma lem1365004 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : (term126 x) = False.
Proof. exact (prop_ext (fun h5 : term126 x => @lem1365003 x h1 h2 h3 h4) (fun h5 : False => @lem1364174 x h4)). Qed.
Lemma lem1365005 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : False.
Proof. exact (EQ_MP (@lem1365004 x h1 h2 h3 h4) (@lem1364174 x h4)). Qed.
Lemma lem1365006 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : term45 = False.
Proof. exact (prop_ext (fun h5 : term45 => @lem1365005 x h1 h2 h3 h4) (fun h5 : False => @lem1364100 h2)). Qed.
Lemma lem1365007 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : False.
Proof. exact (EQ_MP (@lem1365006 x h1 h2 h3 h4) (@lem1364100 h2)). Qed.
Lemma lem1365008 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : (term164 = term22) = False.
Proof. exact (prop_ext (fun h5 : term164 = term22 => @lem1365007 x h1 h2 h3 h4) (fun h5 : False => @lem1364016 h3)). Qed.
Lemma lem1365009 (x : real) (h1 : term62) (h2 : term45) (h3 : term164 = term22) (h4 : term126 x) : False.
Proof. exact (EQ_MP (@lem1365008 x h1 h2 h3 h4) (@lem1364016 h3)). Qed.
Lemma lem1365010 (h1 : term62) (h2 : term45) (h3 : term100) (h4 : term164 = term22) : False.
Proof. exact (ex_elim (@lem1363628 h3) (fun x : real => fun h0 : term136 x => @lem1365009 x h1 h2 h4 h0)). Qed.
Lemma lem1365011 (h1 : term62) (h2 : term45) (h3 : term100) (h4 : term164 = term22) : term45 = False.
Proof. exact (prop_ext (fun h5 : term45 => @lem1365010 h1 h2 h3 h4) (fun h5 : False => @lem1363999 h2)). Qed.
Lemma lem1365012 (h1 : term62) (h2 : term45) (h3 : term100) (h4 : term164 = term22) : False.
Proof. exact (EQ_MP (@lem1365011 h1 h2 h3 h4) (@lem1363999 h2)). Qed.
Lemma lem1365013 (h1 : term62) (h2 : term45) (h3 : term100) (h4 : term164 = term22) : (term164 = term22) = False.
Proof. exact (prop_ext (fun h5 : term164 = term22 => @lem1365012 h1 h2 h3 h4) (fun h5 : False => @lem1363634 h4)). Qed.
Lemma lem1365014 (h1 : term62) (h2 : term45) (h3 : term100) (h4 : term164 = term22) : False.
Proof. exact (EQ_MP (@lem1365013 h1 h2 h3 h4) (@lem1363634 h4)). Qed.
Lemma lem1365015 (h1 : term62) (h2 : term100) (h3 : term164 = term22) : term43.
Proof. exact (fun h0 : term45 => @lem1365014 h1 h0 h2 h3). Qed.
Lemma lem1365016 : term43 = term44.
Proof. exact (@lem69 term45). Qed.
Lemma lem1365017 (h1 : term62) (h2 : term100) (h3 : term164 = term22) : term44.
Proof. exact (EQ_MP (@lem1365016) (@lem1365015 h1 h2 h3)). Qed.
Lemma lem1365018 (h1 : term100) (h2 : term164 = term22) : term48.
Proof. exact (fun h0 : term62 => @lem1365017 h0 h1 h2). Qed.
Lemma lem1365019 (h1 : term100) : term51.
Proof. exact (fun h0 : term164 = term22 => @lem1365018 h1 h0). Qed.
Lemma lem1365020 : term102.
Proof. exact (fun h0 : term100 => @lem1365019 h0). Qed.
Lemma lem1365021 : term39.
Proof. exact (EQ_MP (@lem1363426) (@lem1365020)). Qed.
Lemma lem1365023 : term39.
Proof. exact (@lem1363010 (@lem1365021)). Qed.
Lemma lem1365024 (h1 : term38) : term50.
Proof. exact (@lem1365023 (@lem1362995 h1)). Qed.
Lemma lem1365025 (h1 : term38) : term47.
Proof. exact (@lem1365024 h1 (@lem1362041)). Qed.
Lemma lem1365026 (h1 : term38) : term43.
Proof. exact (@lem1365025 h1 (@lem1339379)). Qed.
Lemma lem1365027 (h1 : term38) : False.
Proof. exact (@lem1365026 h1 (@lem1339697)). Qed.
Lemma lem1365028 (h1 : term38) : term38 = False.
Proof. exact (prop_ext (fun h2 : term38 => @lem1365027 h1) (fun h2 : False => @lem1362995 h1)). Qed.
Lemma lem1365029 (h1 : term38) : False.
Proof. exact (EQ_MP (@lem1365028 h1) (@lem1362995 h1)). Qed.
Lemma lem1365030 : term37.
Proof. exact (fun h0 : term38 => @lem1365029 h0). Qed.
Lemma lem1365031 : term35.
Proof. exact (EQ_MP (@lem1362994) (@lem1365030)). Qed.
Lemma lem1365032 : term34.
Proof. exact (EQ_MP (@lem1362990) (@lem1365031)). Qed.
