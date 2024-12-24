Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_INF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_INF_APPROACH_spec.
Require Import HAS_INF_INF_spec.
Require Import HAS_INF_LBOUND_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_NOT_LT_spec.
Require Import has_inf_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1339577_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367765_spec.
Require Import thm1367770_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981223_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982709_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982725_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1982796_spec.
Require Import thm1982797_spec.
Require Import thm1988285_spec.
Require Import thm1988287_spec.
Require Import thm1988295_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm706951_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5311017 (y : real) (x : real) (h1 : (term0 x y) = (real_le y x)) : (term0 x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem5311018 (y : real) (x : real) (h1 : (term0 x y) = (real_le y x)) : (real_le y x) = (term0 x y).
Proof. exact (SYM (@lem5311017 y x h1)). Qed.
Lemma lem5311019 (x : real) (y : real) (h1 : (real_le y x) = (term0 x y)) : (real_le y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem5311020 (x : real) (y : real) (h1 : (real_le y x) = (term0 x y)) : (term0 x y) = (real_le y x).
Proof. exact (SYM (@lem5311019 x y h1)). Qed.
Lemma lem5311021 (x : real) (y : real) : ((term0 x y) = (real_le y x)) = ((real_le y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_le y x) => @lem5311018 y x h1) (fun h1 : (real_le y x) = (term0 x y) => @lem5311020 x y h1)). Qed.
Lemma lem5311022 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem5311021 x y)). Qed.
Lemma lem5311023 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311024 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem5311023) (@lem5311022 x)). Qed.
Lemma lem5311025 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem5311024 x)). Qed.
Lemma lem5311026 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311027 : term7 = term8.
Proof. exact (MK_COMB (@lem5311026) (@lem5311025)). Qed.
Lemma lem5311028 : term8.
Proof. exact (EQ_MP (@lem5311027) (@lem1376537)). Qed.
Lemma lem5311029 (x : real) : term9 x.
Proof. exact (@lem5311028 x). Qed.
Lemma lem5311030 (x : real) : (term9 x) = (term4 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem5311031 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem5311030 x) (@lem5311029 x)). Qed.
Lemma lem5311032 (x : real) (y : real) : term10 x y.
Proof. exact (@lem5311031 x y). Qed.
Lemma lem5311033 (x : real) (y : real) : (term10 x y) = ((real_le y x) = (term0 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem5311035 (t1 : Prop) : term11 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5311036 (t1 : Prop) : (term11 t1) = (term12 t1).
Proof. exact (eq_refl (term11 t1)). Qed.
Lemma lem5311037 (t1 : Prop) : term12 t1.
Proof. exact (EQ_MP (@lem5311036 t1) (@lem5311035 t1)). Qed.
Lemma lem5311038 (t1 : Prop) (t2 : Prop) : term13 t1 t2.
Proof. exact (@lem5311037 t1 t2). Qed.
Lemma lem5311039 (t1 : Prop) (t2 : Prop) : (term13 t1 t2) = (term14 t1 t2).
Proof. exact (eq_refl (term13 t1 t2)). Qed.
Lemma lem5311040 (t1 : Prop) (t2 : Prop) : term14 t1 t2.
Proof. exact (EQ_MP (@lem5311039 t1 t2) (@lem5311038 t1 t2)). Qed.
Lemma lem5311041 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term15 t1 t2 t3.
Proof. exact (@lem5311040 t1 t2 t3). Qed.
Lemma lem5311042 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term15 t1 t2 t3) = ((term16 t1 t2 t3) = (term17 t1 t2 t3)).
Proof. exact (eq_refl (term15 t1 t2 t3)). Qed.
Lemma lem5311043 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (EQ_MP (@lem5311042 t1 t2 t3) (@lem5311041 t1 t2 t3)). Qed.
Lemma lem5311044 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (SYM (@lem5311043 t1 t2 t3)). Qed.
Lemma lem5311045 (t1 : Prop) : term11 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5311046 (t1 : Prop) : (term11 t1) = (term12 t1).
Proof. exact (eq_refl (term11 t1)). Qed.
Lemma lem5311047 (t1 : Prop) : term12 t1.
Proof. exact (EQ_MP (@lem5311046 t1) (@lem5311045 t1)). Qed.
Lemma lem5311048 (t1 : Prop) (t2 : Prop) : term13 t1 t2.
Proof. exact (@lem5311047 t1 t2). Qed.
Lemma lem5311049 (t1 : Prop) (t2 : Prop) : (term13 t1 t2) = (term14 t1 t2).
Proof. exact (eq_refl (term13 t1 t2)). Qed.
Lemma lem5311050 (t1 : Prop) (t2 : Prop) : term14 t1 t2.
Proof. exact (EQ_MP (@lem5311049 t1 t2) (@lem5311048 t1 t2)). Qed.
Lemma lem5311051 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term15 t1 t2 t3.
Proof. exact (@lem5311050 t1 t2 t3). Qed.
Lemma lem5311052 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term15 t1 t2 t3) = ((term16 t1 t2 t3) = (term17 t1 t2 t3)).
Proof. exact (eq_refl (term15 t1 t2 t3)). Qed.
Lemma lem5311053 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (EQ_MP (@lem5311052 t1 t2 t3) (@lem5311051 t1 t2 t3)). Qed.
Lemma lem5311054 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (SYM (@lem5311053 t1 t2 t3)). Qed.
Lemma lem5311055 (s : real -> Prop) : term18 s.
Proof. exact (@lem5295254 s). Qed.
Lemma lem5311056 (s : real -> Prop) : (term18 s) = (term19 s).
Proof. exact (eq_refl (term18 s)). Qed.
Lemma lem5311057 (s : real -> Prop) : term19 s.
Proof. exact (EQ_MP (@lem5311056 s) (@lem5311055 s)). Qed.
Lemma lem5311058 (s : real -> Prop) (l : real) : term20 s l.
Proof. exact (@lem5311057 s l). Qed.
Lemma lem5311059 (s : real -> Prop) (l : real) : (term20 s l) = ((has_inf s l) = (term21 s l)).
Proof. exact (eq_refl (term20 s l)). Qed.
Lemma lem5311061 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5311063 (s : real -> Prop) (l : real) : (has_inf s l) = (term21 s l).
Proof. exact (EQ_MP (@lem5311059 s l) (@lem5311058 s l)). Qed.
Lemma lem5311082 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term21 s l.
Proof. exact (EQ_MP (@lem5311063 s l) (@lem5311061 s l h1)). Qed.
Lemma lem5311088 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term22 s.
Proof. exact (proj1 (@lem5311082 s l h1)). Qed.
Lemma lem5311089 (s : real -> Prop) : term23 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5311103 (s : real -> Prop) (l : real) (h1 : has_inf s l) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5311089 s (@lem5311088 s l h1)). Qed.
Lemma lem5311104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5311105 (s : real -> Prop) (l : real) (h1 : has_inf s l) : (term22 s) = (~ False).
Proof. exact (MK_COMB (@lem5311104) (@lem5311103 s l h1)). Qed.
Lemma lem5311107 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5311108 (s : real -> Prop) (l : real) (h1 : has_inf s l) : (term22 s) = True.
Proof. exact (TRANS (@lem5311105 s l h1) (@lem5311107)). Qed.
Lemma lem5311109 (s : real -> Prop) (l : real) (h1 : has_inf s l) : True = (term22 s).
Proof. exact (SYM (@lem5311108 s l h1)). Qed.
Lemma lem5311110 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term22 s.
Proof. exact (EQ_MP (@lem5311109 s l h1) (@lem0)). Qed.
Lemma lem5311112 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5311113 (s : real -> Prop) (l : real) : (term25 s l) = (term26 s l).
Proof. exact (@lem5311112 (term25 s l)). Qed.
Lemma lem5311114 (s : real -> Prop) (l : real) : (term26 s l) = (term25 s l).
Proof. exact (SYM (@lem5311113 s l)). Qed.
Lemma lem5311115 (s : real -> Prop) (l : real) (h1 : term27 s l) : term27 s l.
Proof. exact (h1). Qed.
Lemma lem5311118 (s : real -> Prop) (l : real) (h1 : term28 s l) : term28 s l.
Proof. exact (h1). Qed.
Lemma lem5311119 (s : real -> Prop) (l : real) : term29 s l.
Proof. exact (fun h0 : term28 s l => @lem5311118 s l h0). Qed.
Lemma lem5311120 (s : real -> Prop) (l : real) (h1 : term29 s l) : term29 s l.
Proof. exact (h1). Qed.
Lemma lem5311121 (s : real -> Prop) (l : real) (h1 : term28 s l) : term28 s l.
Proof. exact (h1). Qed.
Lemma lem5311122 (s : real -> Prop) (l : real) (h1 : term29 s l) (h2 : term28 s l) : term28 s l.
Proof. exact (@lem5311120 s l h1 (@lem5311121 s l h2)). Qed.
Lemma lem5311123 (s : real -> Prop) (l : real) (h1 : term28 s l) : term30 s l.
Proof. exact (fun h0 : term29 s l => @lem5311122 s l h0 h1). Qed.
Lemma lem5311124 (s : real -> Prop) (l : real) (h1 : term29 s l) : term29 s l.
Proof. exact (h1). Qed.
Lemma lem5311125 (s : real -> Prop) (l : real) (h1 : term29 s l) (h2 : term28 s l) : term28 s l.
Proof. exact (@lem5311123 s l h2 (@lem5311124 s l h1)). Qed.
Lemma lem5311126 (s : real -> Prop) (l : real) (h1 : term29 s l) : term29 s l.
Proof. exact (fun h0 : term28 s l => @lem5311125 s l h1 h0). Qed.
Lemma lem5311127 (s : real -> Prop) (l : real) : term31 s l.
Proof. exact (fun h0 : term29 s l => @lem5311126 s l h0). Qed.
Lemma lem5311130 (s : real -> Prop) (l : real) : term29 s l.
Proof. exact (@lem5311127 s l (@lem5311119 s l)). Qed.
Lemma lem5311150 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5311151 : term32 = term33.
Proof. exact (@lem5311150 term34). Qed.
Lemma lem5311168 (s : real -> Prop) (l : real) : (term35 s l) = (term35 s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5311169 (s : real -> Prop) (l : real) : (term36 s l) = (term37 s l).
Proof. exact (MK_COMB (@lem5311168 s l) (@lem5311151)). Qed.
Lemma lem5311172 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5311173 (s : real -> Prop) (l : real) : (term28 s l) = (term39 s l).
Proof. exact (MK_COMB (@lem5311172 s l) (@lem5311169 s l)). Qed.
Lemma lem5311176 (l : real) : (term40 l) = (term41 l).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311173 s l)). Qed.
Lemma lem5311177 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311178 (l : real) : (term42 l) = (term43 l).
Proof. exact (MK_COMB (@lem5311177) (@lem5311176 l)). Qed.
Lemma lem5311183 : term44 = term45.
Proof. exact (fun_ext (fun l : real => @lem5311178 l)). Qed.
Lemma lem5311184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311193 : term46 = term47.
Proof. exact (MK_COMB (@lem5311184) (@lem5311183)). Qed.
Lemma lem5311202 (s : real -> Prop) (b : real) (x : real) : (term48 s b x) = (term48 s b x).
Proof. exact (eq_refl (term48 s b x)). Qed.
Lemma lem5311203 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5311202 s b x)). Qed.
Lemma lem5311204 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311205 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5311204) (@lem5311203 s b)). Qed.
Lemma lem5311206 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (fun_ext (fun b : real => @lem5311205 s b)). Qed.
Lemma lem5311207 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311208 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem5311207) (@lem5311206 s)). Qed.
Lemma lem5311209 : term53 = term53.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311208 s)). Qed.
Lemma lem5311210 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311211 : term34 = term34.
Proof. exact (MK_COMB (@lem5311210) (@lem5311209)). Qed.
Lemma lem5311212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5311213 : term33 = term33.
Proof. exact (MK_COMB (@lem5311212) (@lem5311211)). Qed.
Lemma lem5311218 (s : real -> Prop) (l : real) (x : real) : (term54 s l x) = (term54 s l x).
Proof. exact (eq_refl (term54 s l x)). Qed.
Lemma lem5311219 (s : real -> Prop) (l : real) : (term55 s l) = (term55 s l).
Proof. exact (fun_ext (fun x : real => @lem5311218 s l x)). Qed.
Lemma lem5311220 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311221 (s : real -> Prop) (l : real) : (term25 s l) = (term25 s l).
Proof. exact (MK_COMB (@lem5311220) (@lem5311219 s l)). Qed.
Lemma lem5311222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5311223 (s : real -> Prop) (l : real) : (term27 s l) = (term27 s l).
Proof. exact (MK_COMB (@lem5311222) (@lem5311221 s l)). Qed.
Lemma lem5311224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5311225 (s : real -> Prop) (l : real) : (term35 s l) = (term35 s l).
Proof. exact (MK_COMB (@lem5311224) (@lem5311223 s l)). Qed.
Lemma lem5311226 (s : real -> Prop) (l : real) : (term37 s l) = (term37 s l).
Proof. exact (MK_COMB (@lem5311225 s l) (@lem5311213)). Qed.
Lemma lem5311229 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5311230 (s : real -> Prop) (l : real) : (term39 s l) = (term39 s l).
Proof. exact (MK_COMB (@lem5311229 s l) (@lem5311226 s l)). Qed.
Lemma lem5311231 (l : real) : (term41 l) = (term41 l).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311230 s l)). Qed.
Lemma lem5311232 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311233 (l : real) : (term43 l) = (term43 l).
Proof. exact (MK_COMB (@lem5311232) (@lem5311231 l)). Qed.
Lemma lem5311234 : term45 = term45.
Proof. exact (fun_ext (fun l : real => @lem5311233 l)). Qed.
Lemma lem5311235 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311236 : term47 = term47.
Proof. exact (MK_COMB (@lem5311235) (@lem5311234)). Qed.
Lemma lem5311285 : term46 = term47.
Proof. exact (TRANS (@lem5311193) (@lem5311236)). Qed.
Lemma lem5311286 : term47 = term46.
Proof. exact (SYM (@lem5311285)). Qed.
Lemma lem5311288 (s : real -> Prop) (l : real) (h1 : term27 s l) : term27 s l.
Proof. exact (h1). Qed.
Lemma lem5311289 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem5311295 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5311302 (s : real -> Prop) (l : real) (x : real) : (term56 s l x) = (term57 s l x).
Proof. exact (@lem17362 (@IN real x s) (real_le l x)). Qed.
Lemma lem5311303 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5311304 (s : real -> Prop) (l : real) : (term27 s l) = (term60 s l).
Proof. exact (@lem5311303 (term55 s l)). Qed.
Lemma lem5311305 (s : real -> Prop) (l : real) (x : real) : (term61 s l x) = (term54 s l x).
Proof. exact (eq_refl (term61 s l x)). Qed.
Lemma lem5311306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5311307 (s : real -> Prop) (l : real) (x : real) : (term62 s l x) = (term56 s l x).
Proof. exact (MK_COMB (@lem5311306) (@lem5311305 s l x)). Qed.
Lemma lem5311308 (s : real -> Prop) (l : real) (x : real) : (term62 s l x) = (term57 s l x).
Proof. exact (TRANS (@lem5311307 s l x) (@lem5311302 s l x)). Qed.
Lemma lem5311309 (s : real -> Prop) (l : real) : (term63 s l) = (term64 s l).
Proof. exact (fun_ext (fun x : real => @lem5311308 s l x)). Qed.
Lemma lem5311310 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5311311 (s : real -> Prop) (l : real) : (term60 s l) = (term65 s l).
Proof. exact (MK_COMB (@lem5311310) (@lem5311309 s l)). Qed.
Lemma lem5311364 (s : real -> Prop) (l : real) : (term27 s l) = (term65 s l).
Proof. exact (TRANS (@lem5311304 s l) (@lem5311311 s l)). Qed.
Lemma lem5311365 (s : real -> Prop) (l : real) (h1 : term27 s l) : term65 s l.
Proof. exact (EQ_MP (@lem5311364 s l) (@lem5311288 s l h1)). Qed.
Lemma lem5311372 (b : real) (x : real) (s : real -> Prop) : (term66 b x s) = (term67 b x s).
Proof. exact (@lem17045 (has_inf s b) (@IN real x s)). Qed.
Lemma lem5311373 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5311374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5311375 (b : real) (x : real) (s : real -> Prop) : (term68 b x s) = (term69 b x s).
Proof. exact (MK_COMB (@lem5311374) (@lem5311372 b x s)). Qed.
Lemma lem5311376 (s : real -> Prop) (b : real) (x : real) : (term70 s b x) = (term71 s b x).
Proof. exact (MK_COMB (@lem5311375 b x s) (@lem5311373 b x)). Qed.
Lemma lem5311377 (s : real -> Prop) (b : real) (x : real) : (term48 s b x) = (term70 s b x).
Proof. exact (@lem17265 (term72 b x s) (real_le b x)). Qed.
Lemma lem5311378 (s : real -> Prop) (b : real) (x : real) : (term48 s b x) = (term71 s b x).
Proof. exact (TRANS (@lem5311377 s b x) (@lem5311376 s b x)). Qed.
Lemma lem5311379 (s : real -> Prop) (b : real) : (term49 s b) = (term73 s b).
Proof. exact (fun_ext (fun x : real => @lem5311378 s b x)). Qed.
Lemma lem5311380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311381 (s : real -> Prop) (b : real) : (term50 s b) = (term74 s b).
Proof. exact (MK_COMB (@lem5311380) (@lem5311379 s b)). Qed.
Lemma lem5311382 (s : real -> Prop) : (term51 s) = (term75 s).
Proof. exact (fun_ext (fun b : real => @lem5311381 s b)). Qed.
Lemma lem5311383 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311384 (s : real -> Prop) : (term52 s) = (term76 s).
Proof. exact (MK_COMB (@lem5311383) (@lem5311382 s)). Qed.
Lemma lem5311385 : term53 = term77.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311384 s)). Qed.
Lemma lem5311386 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311447 : term34 = term78.
Proof. exact (MK_COMB (@lem5311386) (@lem5311385)). Qed.
Lemma lem5311448 (h1 : term34) : term78.
Proof. exact (EQ_MP (@lem5311447) (@lem5311289 h1)). Qed.
Lemma lem5311455 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5311480 (s : real -> Prop) (b : real) (x : real) : (term71 s b x) = (term71 s b x).
Proof. exact (eq_refl (term71 s b x)). Qed.
Lemma lem5311481 (s : real -> Prop) (b : real) : (term73 s b) = (term73 s b).
Proof. exact (fun_ext (fun x : real => @lem5311480 s b x)). Qed.
Lemma lem5311482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311483 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (MK_COMB (@lem5311482) (@lem5311481 s b)). Qed.
Lemma lem5311484 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (fun_ext (fun b : real => @lem5311483 s b)). Qed.
Lemma lem5311485 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311486 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5311485) (@lem5311484 s)). Qed.
Lemma lem5311487 : term77 = term77.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311486 s)). Qed.
Lemma lem5311488 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311489 : term78 = term78.
Proof. exact (MK_COMB (@lem5311488) (@lem5311487)). Qed.
Lemma lem5311490 (h1 : term34) : term78.
Proof. exact (EQ_MP (@lem5311489) (@lem5311448 h1)). Qed.
Lemma lem5311506 (s : real -> Prop) (l : real) (x : real) (h1 : term57 s l x) : term57 s l x.
Proof. exact (h1). Qed.
Lemma lem5311512 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5311526 (s : real -> Prop) (b : real) (x : real) : (term71 s b x) = (term71 s b x).
Proof. exact (eq_refl (term71 s b x)). Qed.
Lemma lem5311527 (s : real -> Prop) (b : real) : (term73 s b) = (term73 s b).
Proof. exact (fun_ext (fun x : real => @lem5311526 s b x)). Qed.
Lemma lem5311528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311529 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (MK_COMB (@lem5311528) (@lem5311527 s b)). Qed.
Lemma lem5311530 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (fun_ext (fun b : real => @lem5311529 s b)). Qed.
Lemma lem5311531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311532 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5311531) (@lem5311530 s)). Qed.
Lemma lem5311533 : term77 = term77.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311532 s)). Qed.
Lemma lem5311534 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311536 : term78 = term78.
Proof. exact (MK_COMB (@lem5311534) (@lem5311533)). Qed.
Lemma lem5311537 (h1 : term34) : term78.
Proof. exact (EQ_MP (@lem5311536) (@lem5311490 h1)). Qed.
Lemma lem5311546 (_69674 : real -> Prop) (h1 : term34) : term79 _69674.
Proof. exact (@lem5311537 h1 _69674). Qed.
Lemma lem5311547 (_69674 : real -> Prop) : (term79 _69674) = (term76 _69674).
Proof. exact (eq_refl (term79 _69674)). Qed.
Lemma lem5311548 (_69674 : real -> Prop) (h1 : term34) : term76 _69674.
Proof. exact (EQ_MP (@lem5311547 _69674) (@lem5311546 _69674 h1)). Qed.
Lemma lem5311549 (_69674 : real -> Prop) (_69675 : real) (h1 : term34) : term80 _69674 _69675.
Proof. exact (@lem5311548 _69674 h1 _69675). Qed.
Lemma lem5311550 (_69674 : real -> Prop) (_69675 : real) : (term80 _69674 _69675) = (term74 _69674 _69675).
Proof. exact (eq_refl (term80 _69674 _69675)). Qed.
Lemma lem5311551 (_69674 : real -> Prop) (_69675 : real) (h1 : term34) : term74 _69674 _69675.
Proof. exact (EQ_MP (@lem5311550 _69674 _69675) (@lem5311549 _69674 _69675 h1)). Qed.
Lemma lem5311552 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) (h1 : term34) : term81 _69674 _69675 _69676.
Proof. exact (@lem5311551 _69674 _69675 h1 _69676). Qed.
Lemma lem5311553 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) : (term81 _69674 _69675 _69676) = (term71 _69674 _69675 _69676).
Proof. exact (eq_refl (term81 _69674 _69675 _69676)). Qed.
Lemma lem5311554 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) (h1 : term34) : term71 _69674 _69675 _69676.
Proof. exact (EQ_MP (@lem5311553 _69674 _69675 _69676) (@lem5311552 _69674 _69675 _69676 h1)). Qed.
Lemma lem5311556 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5311567 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) : (term71 _69674 _69675 _69676) = (term82 _69674 _69675 _69676).
Proof. exact (@lem5311054 (term83 _69674 _69675) (term84 _69676 _69674) (real_le _69675 _69676)). Qed.
Lemma lem5311568 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) (h1 : term34) : term82 _69674 _69675 _69676.
Proof. exact (EQ_MP (@lem5311567 _69674 _69675 _69676) (@lem5311554 _69674 _69675 _69676 h1)). Qed.
Lemma lem5311572 (s : real -> Prop) (l : real) (x : real) (h1 : term57 s l x) : term85 l x.
Proof. exact (proj2 (@lem5311506 s l x h1)). Qed.
Lemma lem5311574 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5311575 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term86 s l.
Proof. exact (fun h0 : term83 s l => @lem5311574 s l h1). Qed.
Lemma lem5311577 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5311578 (s : real -> Prop) (l : real) : (term86 s l) = (has_inf s l).
Proof. exact (@lem5311577 (has_inf s l)). Qed.
Lemma lem5311579 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (EQ_MP (@lem5311578 s l) (@lem5311575 s l h1)). Qed.
Lemma lem5311581 (s : real -> Prop) (l : real) (x : real) (h1 : term57 s l x) : @IN real x s.
Proof. exact (proj1 (@lem5311506 s l x h1)). Qed.
Lemma lem5311582 (s : real -> Prop) (l : real) (x : real) (h1 : term57 s l x) : term88 x s.
Proof. exact (fun h0 : term84 x s => @lem5311581 s l x h1). Qed.
Lemma lem5311584 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5311585 (x : real) (s : real -> Prop) : (term88 x s) = (@IN real x s).
Proof. exact (@lem5311584 (@IN real x s)). Qed.
Lemma lem5311586 (s : real -> Prop) (l : real) (x : real) (h1 : term57 s l x) : @IN real x s.
Proof. exact (EQ_MP (@lem5311585 x s) (@lem5311582 s l x h1)). Qed.
Lemma lem5311592 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5311593 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) : (term82 _69674 _69675 _69676) = (term89 _69674 _69675 _69676).
Proof. exact (@lem5311592 (term84 _69676 _69674) (term83 _69674 _69675) (real_le _69675 _69676)). Qed.
Lemma lem5311607 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5311608 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term90 _69674 _69675 _69676) = (term91 _69676 _69674 _69675).
Proof. exact (@lem5311607 (real_le _69675 _69676) (term83 _69674 _69675)). Qed.
Lemma lem5311614 (_69676 : real) (_69674 : real -> Prop) : (term92 _69676 _69674) = (term92 _69676 _69674).
Proof. exact (eq_refl (term92 _69676 _69674)). Qed.
Lemma lem5311615 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term89 _69674 _69675 _69676) = (term93 _69676 _69674 _69675).
Proof. exact (MK_COMB (@lem5311614 _69676 _69674) (@lem5311608 _69676 _69674 _69675)). Qed.
Lemma lem5311619 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5311620 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term93 _69676 _69674 _69675) = (term94 _69676 _69674 _69675).
Proof. exact (@lem5311619 (real_le _69675 _69676) (term84 _69676 _69674) (term83 _69674 _69675)). Qed.
Lemma lem5311636 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term89 _69674 _69675 _69676) = (term94 _69676 _69674 _69675).
Proof. exact (TRANS (@lem5311615 _69676 _69674 _69675) (@lem5311620 _69676 _69674 _69675)). Qed.
Lemma lem5311637 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term82 _69674 _69675 _69676) = (term94 _69676 _69674 _69675).
Proof. exact (TRANS (@lem5311593 _69674 _69675 _69676) (@lem5311636 _69676 _69674 _69675)). Qed.
Lemma lem5311638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5311639 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term95 _69674 _69675 _69676) = (term96 _69676 _69674 _69675).
Proof. exact (MK_COMB (@lem5311638) (@lem5311637 _69676 _69674 _69675)). Qed.
Lemma lem5311653 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5311654 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term67 _69675 _69676 _69674) = (term97 _69676 _69674 _69675).
Proof. exact (@lem5311653 (term84 _69676 _69674) (term83 _69674 _69675)). Qed.
Lemma lem5311660 (_69675 : real) (_69676 : real) : (term98 _69675 _69676) = (term98 _69675 _69676).
Proof. exact (eq_refl (term98 _69675 _69676)). Qed.
Lemma lem5311661 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : (term99 _69675 _69676 _69674) = (term94 _69676 _69674 _69675).
Proof. exact (MK_COMB (@lem5311660 _69675 _69676) (@lem5311654 _69676 _69674 _69675)). Qed.
Lemma lem5311672 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : ((term82 _69674 _69675 _69676) = (term99 _69675 _69676 _69674)) = ((term94 _69676 _69674 _69675) = (term94 _69676 _69674 _69675)).
Proof. exact (MK_COMB (@lem5311639 _69676 _69674 _69675) (@lem5311661 _69676 _69674 _69675)). Qed.
Lemma lem5311674 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5311675 (x : Prop) : (x = x) = True.
Proof. exact (@lem5311674 Prop x). Qed.
Lemma lem5311676 (_69676 : real) (_69674 : real -> Prop) (_69675 : real) : ((term94 _69676 _69674 _69675) = (term94 _69676 _69674 _69675)) = True.
Proof. exact (@lem5311675 (term94 _69676 _69674 _69675)). Qed.
Lemma lem5311677 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : ((term82 _69674 _69675 _69676) = (term99 _69675 _69676 _69674)) = True.
Proof. exact (TRANS (@lem5311672 _69676 _69674 _69675) (@lem5311676 _69676 _69674 _69675)). Qed.
Lemma lem5311678 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : True = ((term82 _69674 _69675 _69676) = (term99 _69675 _69676 _69674)).
Proof. exact (SYM (@lem5311677 _69675 _69676 _69674)). Qed.
Lemma lem5311679 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : (term82 _69674 _69675 _69676) = (term99 _69675 _69676 _69674).
Proof. exact (EQ_MP (@lem5311678 _69675 _69676 _69674) (@lem0)). Qed.
Lemma lem5311680 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) (h1 : term34) : term99 _69675 _69676 _69674.
Proof. exact (EQ_MP (@lem5311679 _69675 _69676 _69674) (@lem5311568 _69674 _69675 _69676 h1)). Qed.
Lemma lem5311682 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5311683 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) : (term99 _69675 _69676 _69674) = (term101 _69674 _69675 _69676).
Proof. exact (@lem5311682 (term67 _69675 _69676 _69674) (real_le _69675 _69676)). Qed.
Lemma lem5311685 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5311686 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : (term104 _69675 _69676 _69674) = (term105 _69675 _69676 _69674).
Proof. exact (@lem5311685 (term83 _69674 _69675) (term84 _69676 _69674)). Qed.
Lemma lem5311688 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5311689 (_69674 : real -> Prop) (_69675 : real) : (term107 _69674 _69675) = (has_inf _69674 _69675).
Proof. exact (@lem5311688 (has_inf _69674 _69675)). Qed.
Lemma lem5311690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5311691 (_69674 : real -> Prop) (_69675 : real) : (term108 _69674 _69675) = (term109 _69674 _69675).
Proof. exact (MK_COMB (@lem5311690) (@lem5311689 _69674 _69675)). Qed.
Lemma lem5311693 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5311694 (_69676 : real) (_69674 : real -> Prop) : (term110 _69676 _69674) = (@IN real _69676 _69674).
Proof. exact (@lem5311693 (@IN real _69676 _69674)). Qed.
Lemma lem5311695 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : (term105 _69675 _69676 _69674) = (term72 _69675 _69676 _69674).
Proof. exact (MK_COMB (@lem5311691 _69674 _69675) (@lem5311694 _69676 _69674)). Qed.
Lemma lem5311696 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : (term104 _69675 _69676 _69674) = (term72 _69675 _69676 _69674).
Proof. exact (TRANS (@lem5311686 _69675 _69676 _69674) (@lem5311695 _69675 _69676 _69674)). Qed.
Lemma lem5311697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5311698 (_69675 : real) (_69676 : real) (_69674 : real -> Prop) : (term111 _69675 _69676 _69674) = (term112 _69675 _69676 _69674).
Proof. exact (MK_COMB (@lem5311697) (@lem5311696 _69675 _69676 _69674)). Qed.
Lemma lem5311699 (_69675 : real) (_69676 : real) : (real_le _69675 _69676) = (real_le _69675 _69676).
Proof. exact (eq_refl (real_le _69675 _69676)). Qed.
Lemma lem5311700 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) : (term101 _69674 _69675 _69676) = (term48 _69674 _69675 _69676).
Proof. exact (MK_COMB (@lem5311698 _69675 _69676 _69674) (@lem5311699 _69675 _69676)). Qed.
Lemma lem5311701 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) : (term99 _69675 _69676 _69674) = (term48 _69674 _69675 _69676).
Proof. exact (TRANS (@lem5311683 _69674 _69675 _69676) (@lem5311700 _69674 _69675 _69676)). Qed.
Lemma lem5311703 (x : real) (s : real -> Prop) (l : real) (h1 : term57 s l x) (h2 : has_inf s l) : term72 l x s.
Proof. exact (conj (@lem5311579 s l h2) (@lem5311586 s l x h1)). Qed.
Lemma lem5311705 (_69674 : real -> Prop) (_69675 : real) (_69676 : real) (h1 : term34) : term48 _69674 _69675 _69676.
Proof. exact (EQ_MP (@lem5311701 _69674 _69675 _69676) (@lem5311680 _69675 _69676 _69674 h1)). Qed.
Lemma lem5311706 (s : real -> Prop) (l : real) (x : real) (h1 : term34) : term48 s l x.
Proof. exact (@lem5311705 s l x h1). Qed.
Lemma lem5311709 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : real_le l x.
Proof. exact (@lem5311706 s l x h1 (@lem5311703 x s l h2 h3)). Qed.
Lemma lem5311710 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : term113 l x.
Proof. exact (fun h0 : term85 l x => @lem5311709 x s l h1 h2 h3). Qed.
Lemma lem5311712 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5311713 (l : real) (x : real) : (term113 l x) = (real_le l x).
Proof. exact (@lem5311712 (real_le l x)). Qed.
Lemma lem5311714 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : real_le l x.
Proof. exact (EQ_MP (@lem5311713 l x) (@lem5311710 x s l h1 h2 h3)). Qed.
Lemma lem5311717 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5311719 (l : real) (x : real) : (term85 l x) = (term114 l x).
Proof. exact (@lem5311717 (real_le l x)). Qed.
Lemma lem5311722 (s : real -> Prop) (l : real) (x : real) (h1 : term57 s l x) : term114 l x.
Proof. exact (EQ_MP (@lem5311719 l x) (@lem5311572 s l x h1)). Qed.
Lemma lem5311725 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (@lem5311722 s l x h2 (@lem5311714 x s l h1 h2 h3)). Qed.
Lemma lem5311726 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : term115.
Proof. exact (fun h0 : ~ False => @lem5311725 x s l h1 h2 h3). Qed.
Lemma lem5311728 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5311729 : term115 = False.
Proof. exact (@lem5311728 False). Qed.
Lemma lem5311730 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311729) (@lem5311726 x s l h1 h2 h3)). Qed.
Lemma lem5311731 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5311730 x s l h1 h2 h3) (fun h4 : False => @lem5311556 s l h3)). Qed.
Lemma lem5311732 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311731 x s l h1 h2 h3) (@lem5311556 s l h3)). Qed.
Lemma lem5311733 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5311732 x s l h1 h2 h3) (fun h4 : False => @lem5311512 s l h3)). Qed.
Lemma lem5311734 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311733 x s l h1 h2 h3) (@lem5311512 s l h3)). Qed.
Lemma lem5311735 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5311734 x s l h1 h2 h3) (fun h4 : False => @lem5311512 s l h3)). Qed.
Lemma lem5311736 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311735 x s l h1 h2 h3) (@lem5311512 s l h3)). Qed.
Lemma lem5311737 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : (term57 s l x) = False.
Proof. exact (prop_ext (fun h4 : term57 s l x => @lem5311736 x s l h1 h2 h3) (fun h4 : False => @lem5311506 s l x h2)). Qed.
Lemma lem5311738 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311737 x s l h1 h2 h3) (@lem5311506 s l x h2)). Qed.
Lemma lem5311739 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5311738 x s l h1 h2 h3) (fun h4 : False => @lem5311455 s l h3)). Qed.
Lemma lem5311740 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s l x) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311739 x s l h1 h2 h3) (@lem5311455 s l h3)). Qed.
Lemma lem5311741 (s : real -> Prop) (l : real) (h1 : term34) (h2 : term27 s l) (h3 : has_inf s l) : False.
Proof. exact (ex_elim (@lem5311365 s l h2) (fun x : real => fun h0 : term64 s l x => @lem5311740 x s l h1 h0 h3)). Qed.
Lemma lem5311742 (s : real -> Prop) (l : real) (h1 : term34) (h2 : term27 s l) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5311741 s l h1 h2 h3) (fun h4 : False => @lem5311295 s l h3)). Qed.
Lemma lem5311743 (s : real -> Prop) (l : real) (h1 : term34) (h2 : term27 s l) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311742 s l h1 h2 h3) (@lem5311295 s l h3)). Qed.
Lemma lem5311744 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_inf s l) : term32.
Proof. exact (fun h0 : term34 => @lem5311743 s l h0 h1 h2). Qed.
Lemma lem5311745 : term32 = term33.
Proof. exact (@lem69 term34). Qed.
Lemma lem5311746 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_inf s l) : term33.
Proof. exact (EQ_MP (@lem5311745) (@lem5311744 s l h1 h2)). Qed.
Lemma lem5311747 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term37 s l.
Proof. exact (fun h0 : term27 s l => @lem5311746 s l h0 h1). Qed.
Lemma lem5311748 (s : real -> Prop) (l : real) : term39 s l.
Proof. exact (fun h0 : has_inf s l => @lem5311747 s l h0). Qed.
Lemma lem5311753 (l : real) : term43 l.
Proof. exact (fun s : real -> Prop => @lem5311748 s l). Qed.
Lemma lem5311758 : term47.
Proof. exact (fun l : real => @lem5311753 l). Qed.
Lemma lem5311759 : term46.
Proof. exact (EQ_MP (@lem5311286) (@lem5311758)). Qed.
Lemma lem5311760 (l : real) : term116 l.
Proof. exact (@lem5311759 l). Qed.
Lemma lem5311761 (l : real) : (term116 l) = (term42 l).
Proof. exact (eq_refl (term116 l)). Qed.
Lemma lem5311762 (l : real) : term42 l.
Proof. exact (EQ_MP (@lem5311761 l) (@lem5311760 l)). Qed.
Lemma lem5311763 (l : real) (s : real -> Prop) : term117 l s.
Proof. exact (@lem5311762 l s). Qed.
Lemma lem5311764 (s : real -> Prop) (l : real) : (term117 l s) = (term28 s l).
Proof. exact (eq_refl (term117 l s)). Qed.
Lemma lem5311765 (s : real -> Prop) (l : real) : term28 s l.
Proof. exact (EQ_MP (@lem5311764 s l) (@lem5311763 l s)). Qed.
Lemma lem5311767 (s : real -> Prop) (l : real) : term28 s l.
Proof. exact (@lem5311130 s l (@lem5311765 s l)). Qed.
Lemma lem5311768 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term36 s l.
Proof. exact (@lem5311767 s l (@lem5311061 s l h1)). Qed.
Lemma lem5311769 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_inf s l) : term32.
Proof. exact (@lem5311768 s l h2 (@lem5311115 s l h1)). Qed.
Lemma lem5311770 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_inf s l) : False.
Proof. exact (@lem5311769 s l h1 h2 (@lem5292278)). Qed.
Lemma lem5311771 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_inf s l) : (term27 s l) = False.
Proof. exact (prop_ext (fun h3 : term27 s l => @lem5311770 s l h1 h2) (fun h3 : False => @lem5311115 s l h1)). Qed.
Lemma lem5311772 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5311771 s l h1 h2) (@lem5311115 s l h1)). Qed.
Lemma lem5311773 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term26 s l.
Proof. exact (fun h0 : term27 s l => @lem5311772 s l h0 h1). Qed.
Lemma lem5311774 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term25 s l.
Proof. exact (EQ_MP (@lem5311114 s l) (@lem5311773 s l h1)). Qed.
Lemma lem5311776 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5311777 (l : real) (s : real -> Prop) : (term118 l s) = (term119 l s).
Proof. exact (@lem5311776 (term118 l s)). Qed.
Lemma lem5311778 (l : real) (s : real -> Prop) : (term119 l s) = (term118 l s).
Proof. exact (SYM (@lem5311777 l s)). Qed.
Lemma lem5311779 (l : real) (s : real -> Prop) (h1 : term120 l s) : term120 l s.
Proof. exact (h1). Qed.
Lemma lem5311782 (l : real) (s : real -> Prop) (h1 : term121 l s) : term121 l s.
Proof. exact (h1). Qed.
Lemma lem5311783 (l : real) (s : real -> Prop) : term122 l s.
Proof. exact (fun h0 : term121 l s => @lem5311782 l s h0). Qed.
Lemma lem5311784 (l : real) (s : real -> Prop) (h1 : term122 l s) : term122 l s.
Proof. exact (h1). Qed.
Lemma lem5311785 (l : real) (s : real -> Prop) (h1 : term121 l s) : term121 l s.
Proof. exact (h1). Qed.
Lemma lem5311786 (l : real) (s : real -> Prop) (h1 : term122 l s) (h2 : term121 l s) : term121 l s.
Proof. exact (@lem5311784 l s h1 (@lem5311785 l s h2)). Qed.
Lemma lem5311787 (l : real) (s : real -> Prop) (h1 : term121 l s) : term123 l s.
Proof. exact (fun h0 : term122 l s => @lem5311786 l s h0 h1). Qed.
Lemma lem5311788 (l : real) (s : real -> Prop) (h1 : term122 l s) : term122 l s.
Proof. exact (h1). Qed.
Lemma lem5311789 (l : real) (s : real -> Prop) (h1 : term122 l s) (h2 : term121 l s) : term121 l s.
Proof. exact (@lem5311787 l s h2 (@lem5311788 l s h1)). Qed.
Lemma lem5311790 (l : real) (s : real -> Prop) (h1 : term122 l s) : term122 l s.
Proof. exact (fun h0 : term121 l s => @lem5311789 l s h1 h0). Qed.
Lemma lem5311791 (l : real) (s : real -> Prop) : term124 l s.
Proof. exact (fun h0 : term122 l s => @lem5311790 l s h0). Qed.
Lemma lem5311794 (l : real) (s : real -> Prop) : term122 l s.
Proof. exact (@lem5311791 l s (@lem5311783 l s)). Qed.
Lemma lem5311864 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5311865 : term125 = term126.
Proof. exact (@lem5311864 term127). Qed.
Lemma lem5311932 (l : real) (s : real -> Prop) : (term128 l s) = (term128 l s).
Proof. exact (eq_refl (term128 l s)). Qed.
Lemma lem5311933 (l : real) (s : real -> Prop) : (term129 l s) = (term130 l s).
Proof. exact (MK_COMB (@lem5311932 l s) (@lem5311865)). Qed.
Lemma lem5311936 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5311937 (l : real) (s : real -> Prop) : (term121 l s) = (term131 l s).
Proof. exact (MK_COMB (@lem5311936 s l) (@lem5311933 l s)). Qed.
Lemma lem5311940 (s : real -> Prop) : (term132 s) = (term133 s).
Proof. exact (fun_ext (fun l : real => @lem5311937 l s)). Qed.
Lemma lem5311941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311942 (s : real -> Prop) : (term134 s) = (term135 s).
Proof. exact (MK_COMB (@lem5311941) (@lem5311940 s)). Qed.
Lemma lem5311947 : term136 = term137.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311942 s)). Qed.
Lemma lem5311948 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311957 : term138 = term139.
Proof. exact (MK_COMB (@lem5311948) (@lem5311947)). Qed.
Lemma lem5311962 (s : real -> Prop) (x : real) (c : real) : (term140 s x c) = (term140 s x c).
Proof. exact (eq_refl (term140 s x c)). Qed.
Lemma lem5311963 (s : real -> Prop) (c : real) : (term141 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5311962 s x c)). Qed.
Lemma lem5311964 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5311965 (s : real -> Prop) (c : real) : (term142 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5311964) (@lem5311963 s c)). Qed.
Lemma lem5311972 (s : real -> Prop) (l : real) (c : real) : (term143 s l c) = (term143 s l c).
Proof. exact (eq_refl (term143 s l c)). Qed.
Lemma lem5311973 (l : real) (s : real -> Prop) (c : real) : (term144 l s c) = (term144 l s c).
Proof. exact (MK_COMB (@lem5311972 s l c) (@lem5311965 s c)). Qed.
Lemma lem5311974 (l : real) (s : real -> Prop) : (term145 l s) = (term145 l s).
Proof. exact (fun_ext (fun c : real => @lem5311973 l s c)). Qed.
Lemma lem5311975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311976 (l : real) (s : real -> Prop) : (term146 l s) = (term146 l s).
Proof. exact (MK_COMB (@lem5311975) (@lem5311974 l s)). Qed.
Lemma lem5311977 (s : real -> Prop) : (term147 s) = (term147 s).
Proof. exact (fun_ext (fun l : real => @lem5311976 l s)). Qed.
Lemma lem5311978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311979 (s : real -> Prop) : (term148 s) = (term148 s).
Proof. exact (MK_COMB (@lem5311978) (@lem5311977 s)). Qed.
Lemma lem5311980 : term149 = term149.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5311979 s)). Qed.
Lemma lem5311981 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5311982 : term127 = term127.
Proof. exact (MK_COMB (@lem5311981) (@lem5311980)). Qed.
Lemma lem5311983 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5311984 : term126 = term126.
Proof. exact (MK_COMB (@lem5311983) (@lem5311982)). Qed.
Lemma lem5311989 (s : real -> Prop) (x : real) (c : real) : (term140 s x c) = (term140 s x c).
Proof. exact (eq_refl (term140 s x c)). Qed.
Lemma lem5311990 (s : real -> Prop) (c : real) : (term141 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5311989 s x c)). Qed.
Lemma lem5311991 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5311992 (s : real -> Prop) (c : real) : (term142 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5311991) (@lem5311990 s c)). Qed.
Lemma lem5311995 (l : real) (c : real) : (term150 l c) = (term150 l c).
Proof. exact (eq_refl (term150 l c)). Qed.
Lemma lem5311996 (l : real) (s : real -> Prop) (c : real) : (term151 l s c) = (term151 l s c).
Proof. exact (MK_COMB (@lem5311995 l c) (@lem5311992 s c)). Qed.
Lemma lem5311997 (l : real) (s : real -> Prop) : (term152 l s) = (term152 l s).
Proof. exact (fun_ext (fun c : real => @lem5311996 l s c)). Qed.
Lemma lem5311998 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5311999 (l : real) (s : real -> Prop) : (term118 l s) = (term118 l s).
Proof. exact (MK_COMB (@lem5311998) (@lem5311997 l s)). Qed.
Lemma lem5312000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5312001 (l : real) (s : real -> Prop) : (term120 l s) = (term120 l s).
Proof. exact (MK_COMB (@lem5312000) (@lem5311999 l s)). Qed.
Lemma lem5312002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5312003 (l : real) (s : real -> Prop) : (term128 l s) = (term128 l s).
Proof. exact (MK_COMB (@lem5312002) (@lem5312001 l s)). Qed.
Lemma lem5312004 (l : real) (s : real -> Prop) : (term130 l s) = (term130 l s).
Proof. exact (MK_COMB (@lem5312003 l s) (@lem5311984)). Qed.
Lemma lem5312007 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5312008 (l : real) (s : real -> Prop) : (term131 l s) = (term131 l s).
Proof. exact (MK_COMB (@lem5312007 s l) (@lem5312004 l s)). Qed.
Lemma lem5312009 (s : real -> Prop) : (term133 s) = (term133 s).
Proof. exact (fun_ext (fun l : real => @lem5312008 l s)). Qed.
Lemma lem5312010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312011 (s : real -> Prop) : (term135 s) = (term135 s).
Proof. exact (MK_COMB (@lem5312010) (@lem5312009 s)). Qed.
Lemma lem5312012 : term137 = term137.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312011 s)). Qed.
Lemma lem5312013 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312014 : term139 = term139.
Proof. exact (MK_COMB (@lem5312013) (@lem5312012)). Qed.
Lemma lem5312079 : term138 = term139.
Proof. exact (TRANS (@lem5311957) (@lem5312014)). Qed.
Lemma lem5312080 : term139 = term138.
Proof. exact (SYM (@lem5312079)). Qed.
Lemma lem5312082 (l : real) (s : real -> Prop) (h1 : term120 l s) : term120 l s.
Proof. exact (h1). Qed.
Lemma lem5312083 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem5312089 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5312097 (s : real -> Prop) (x : real) (c : real) : (term153 s x c) = (term154 s x c).
Proof. exact (@lem17045 (@IN real x s) (real_lt x c)). Qed.
Lemma lem5312098 (P : real -> Prop) : (term155 P) = (term156 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5312099 (s : real -> Prop) (c : real) : (term157 s c) = (term158 s c).
Proof. exact (@lem5312098 (term141 s c)). Qed.
Lemma lem5312100 (s : real -> Prop) (x : real) (c : real) : (term159 s c x) = (term140 s x c).
Proof. exact (eq_refl (term159 s c x)). Qed.
Lemma lem5312101 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5312102 (s : real -> Prop) (x : real) (c : real) : (term160 s c x) = (term153 s x c).
Proof. exact (MK_COMB (@lem5312101) (@lem5312100 s x c)). Qed.
Lemma lem5312103 (s : real -> Prop) (x : real) (c : real) : (term160 s c x) = (term154 s x c).
Proof. exact (TRANS (@lem5312102 s x c) (@lem5312097 s x c)). Qed.
Lemma lem5312104 (s : real -> Prop) (c : real) : (term161 s c) = (term162 s c).
Proof. exact (fun_ext (fun x : real => @lem5312103 s x c)). Qed.
Lemma lem5312105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312106 (s : real -> Prop) (c : real) : (term158 s c) = (term163 s c).
Proof. exact (MK_COMB (@lem5312105) (@lem5312104 s c)). Qed.
Lemma lem5312107 (s : real -> Prop) (c : real) : (term157 s c) = (term163 s c).
Proof. exact (TRANS (@lem5312099 s c) (@lem5312106 s c)). Qed.
Lemma lem5312109 (l : real) (c : real) : (term164 l c) = (term164 l c).
Proof. exact (eq_refl (term164 l c)). Qed.
Lemma lem5312110 (l : real) (s : real -> Prop) (c : real) : (term165 l s c) = (term166 l s c).
Proof. exact (MK_COMB (@lem5312109 l c) (@lem5312107 s c)). Qed.
Lemma lem5312111 (l : real) (s : real -> Prop) (c : real) : (term167 l s c) = (term165 l s c).
Proof. exact (@lem17362 (real_lt l c) (term142 s c)). Qed.
Lemma lem5312112 (l : real) (s : real -> Prop) (c : real) : (term167 l s c) = (term166 l s c).
Proof. exact (TRANS (@lem5312111 l s c) (@lem5312110 l s c)). Qed.
Lemma lem5312113 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5312114 (l : real) (s : real -> Prop) : (term120 l s) = (term168 l s).
Proof. exact (@lem5312113 (term152 l s)). Qed.
Lemma lem5312115 (l : real) (s : real -> Prop) (c : real) : (term169 l s c) = (term151 l s c).
Proof. exact (eq_refl (term169 l s c)). Qed.
Lemma lem5312116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5312117 (l : real) (s : real -> Prop) (c : real) : (term170 l s c) = (term167 l s c).
Proof. exact (MK_COMB (@lem5312116) (@lem5312115 l s c)). Qed.
Lemma lem5312118 (l : real) (s : real -> Prop) (c : real) : (term170 l s c) = (term166 l s c).
Proof. exact (TRANS (@lem5312117 l s c) (@lem5312112 l s c)). Qed.
Lemma lem5312119 (l : real) (s : real -> Prop) : (term171 l s) = (term172 l s).
Proof. exact (fun_ext (fun c : real => @lem5312118 l s c)). Qed.
Lemma lem5312120 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5312121 (l : real) (s : real -> Prop) : (term168 l s) = (term173 l s).
Proof. exact (MK_COMB (@lem5312120) (@lem5312119 l s)). Qed.
Lemma lem5312222 (l : real) (s : real -> Prop) : (term120 l s) = (term173 l s).
Proof. exact (TRANS (@lem5312114 l s) (@lem5312121 l s)). Qed.
Lemma lem5312223 (l : real) (s : real -> Prop) (h1 : term120 l s) : term173 l s.
Proof. exact (EQ_MP (@lem5312222 l s) (@lem5312082 l s h1)). Qed.
Lemma lem5312230 (s : real -> Prop) (l : real) (c : real) : (term174 s l c) = (term175 s l c).
Proof. exact (@lem17045 (has_inf s l) (real_lt l c)). Qed.
Lemma lem5312235 (s : real -> Prop) (x : real) (c : real) : (term140 s x c) = (term140 s x c).
Proof. exact (eq_refl (term140 s x c)). Qed.
Lemma lem5312236 (s : real -> Prop) (c : real) : (term141 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5312235 s x c)). Qed.
Lemma lem5312237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5312238 (s : real -> Prop) (c : real) : (term142 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5312237) (@lem5312236 s c)). Qed.
Lemma lem5312239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5312240 (s : real -> Prop) (l : real) (c : real) : (term176 s l c) = (term177 s l c).
Proof. exact (MK_COMB (@lem5312239) (@lem5312230 s l c)). Qed.
Lemma lem5312241 (l : real) (s : real -> Prop) (c : real) : (term178 l s c) = (term179 l s c).
Proof. exact (MK_COMB (@lem5312240 s l c) (@lem5312238 s c)). Qed.
Lemma lem5312242 (l : real) (s : real -> Prop) (c : real) : (term144 l s c) = (term178 l s c).
Proof. exact (@lem17265 (term180 s l c) (term142 s c)). Qed.
Lemma lem5312243 (l : real) (s : real -> Prop) (c : real) : (term144 l s c) = (term179 l s c).
Proof. exact (TRANS (@lem5312242 l s c) (@lem5312241 l s c)). Qed.
Lemma lem5312244 (l : real) (s : real -> Prop) : (term145 l s) = (term181 l s).
Proof. exact (fun_ext (fun c : real => @lem5312243 l s c)). Qed.
Lemma lem5312245 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312246 (l : real) (s : real -> Prop) : (term146 l s) = (term182 l s).
Proof. exact (MK_COMB (@lem5312245) (@lem5312244 l s)). Qed.
Lemma lem5312247 (s : real -> Prop) : (term147 s) = (term183 s).
Proof. exact (fun_ext (fun l : real => @lem5312246 l s)). Qed.
Lemma lem5312248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312249 (s : real -> Prop) : (term148 s) = (term184 s).
Proof. exact (MK_COMB (@lem5312248) (@lem5312247 s)). Qed.
Lemma lem5312250 : term149 = term185.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312249 s)). Qed.
Lemma lem5312251 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312252 : term127 = term186.
Proof. exact (MK_COMB (@lem5312251) (@lem5312250)). Qed.
Lemma lem5312359 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5312360 (P : Prop) (Q : real -> Prop) : (term189 P Q) = (term190 P Q).
Proof. exact (@lem5312359 real P Q). Qed.
Lemma lem5312361 (l : real) (s : real -> Prop) (c : real) : (term191 l s c) = (term192 l s c).
Proof. exact (@lem5312360 (term175 s l c) (term141 s c)). Qed.
Lemma lem5312362 (s : real -> Prop) (x : real) (c : real) : (term159 s c x) = (term140 s x c).
Proof. exact (eq_refl (term159 s c x)). Qed.
Lemma lem5312363 (s : real -> Prop) (c : real) : (term193 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5312362 s x c)). Qed.
Lemma lem5312364 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5312365 (s : real -> Prop) (c : real) : (term194 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5312364) (@lem5312363 s c)). Qed.
Lemma lem5312366 (s : real -> Prop) (l : real) (c : real) : (term177 s l c) = (term177 s l c).
Proof. exact (eq_refl (term177 s l c)). Qed.
Lemma lem5312367 (l : real) (s : real -> Prop) (c : real) : (term191 l s c) = (term179 l s c).
Proof. exact (MK_COMB (@lem5312366 s l c) (@lem5312365 s c)). Qed.
Lemma lem5312368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5312369 (l : real) (s : real -> Prop) (c : real) : (term195 l s c) = (term196 l s c).
Proof. exact (MK_COMB (@lem5312368) (@lem5312367 l s c)). Qed.
Lemma lem5312370 (s : real -> Prop) (x : real) (c : real) : (term159 s c x) = (term140 s x c).
Proof. exact (eq_refl (term159 s c x)). Qed.
Lemma lem5312371 (s : real -> Prop) (l : real) (c : real) : (term177 s l c) = (term177 s l c).
Proof. exact (eq_refl (term177 s l c)). Qed.
Lemma lem5312372 (l : real) (s : real -> Prop) (x : real) (c : real) : (term197 l s c x) = (term198 l s x c).
Proof. exact (MK_COMB (@lem5312371 s l c) (@lem5312370 s x c)). Qed.
Lemma lem5312373 (l : real) (s : real -> Prop) (c : real) : (term199 l s c) = (term200 l s c).
Proof. exact (fun_ext (fun x : real => @lem5312372 l s x c)). Qed.
Lemma lem5312374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5312375 (l : real) (s : real -> Prop) (c : real) : (term192 l s c) = (term201 l s c).
Proof. exact (MK_COMB (@lem5312374) (@lem5312373 l s c)). Qed.
Lemma lem5312376 (l : real) (s : real -> Prop) (c : real) : ((term191 l s c) = (term192 l s c)) = ((term179 l s c) = (term201 l s c)).
Proof. exact (MK_COMB (@lem5312369 l s c) (@lem5312375 l s c)). Qed.
Lemma lem5312377 (l : real) (s : real -> Prop) (c : real) : (term179 l s c) = (term201 l s c).
Proof. exact (EQ_MP (@lem5312376 l s c) (@lem5312361 l s c)). Qed.
Lemma lem5312378 (l : real) (s : real -> Prop) : (term181 l s) = (term202 l s).
Proof. exact (fun_ext (fun c : real => @lem5312377 l s c)). Qed.
Lemma lem5312379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312380 (l : real) (s : real -> Prop) : (term182 l s) = (term203 l s).
Proof. exact (MK_COMB (@lem5312379) (@lem5312378 l s)). Qed.
Lemma lem5312382 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5312383 (P : type1626) : (term206 P) = (term207 P).
Proof. exact (@lem5312382 real real P). Qed.
Lemma lem5312384 (l : real) (s : real -> Prop) : (term208 l s) = (term209 l s).
Proof. exact (@lem5312383 (term210 l s)). Qed.
Lemma lem5312385 (l : real) (s : real -> Prop) (c : real) : (term211 l s c) = (term200 l s c).
Proof. exact (eq_refl (term211 l s c)). Qed.
Lemma lem5312386 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5312387 (l : real) (s : real -> Prop) (c : real) (x : real) : (term212 l s c x) = (term213 l s c x).
Proof. exact (MK_COMB (@lem5312385 l s c) (@lem5312386 x)). Qed.
Lemma lem5312388 (l : real) (s : real -> Prop) (x : real) (c : real) : (term213 l s c x) = (term198 l s x c).
Proof. exact (eq_refl (term213 l s c x)). Qed.
Lemma lem5312389 (l : real) (s : real -> Prop) (x : real) (c : real) : (term212 l s c x) = (term198 l s x c).
Proof. exact (TRANS (@lem5312387 l s c x) (@lem5312388 l s x c)). Qed.
Lemma lem5312390 (l : real) (s : real -> Prop) (c : real) : (term214 l s c) = (term200 l s c).
Proof. exact (fun_ext (fun x : real => @lem5312389 l s x c)). Qed.
Lemma lem5312391 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5312392 (l : real) (s : real -> Prop) (c : real) : (term215 l s c) = (term201 l s c).
Proof. exact (MK_COMB (@lem5312391) (@lem5312390 l s c)). Qed.
Lemma lem5312393 (l : real) (s : real -> Prop) : (term216 l s) = (term202 l s).
Proof. exact (fun_ext (fun c : real => @lem5312392 l s c)). Qed.
Lemma lem5312394 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312395 (l : real) (s : real -> Prop) : (term208 l s) = (term203 l s).
Proof. exact (MK_COMB (@lem5312394) (@lem5312393 l s)). Qed.
Lemma lem5312396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5312397 (l : real) (s : real -> Prop) : (term217 l s) = (term218 l s).
Proof. exact (MK_COMB (@lem5312396) (@lem5312395 l s)). Qed.
Lemma lem5312398 (l : real) (s : real -> Prop) (c : real) : (term211 l s c) = (term200 l s c).
Proof. exact (eq_refl (term211 l s c)). Qed.
Lemma lem5312399 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5312400 (l : real) (s : real -> Prop) (x : real -> real) (c : real) : (term219 l s x c) = (term220 l s x c).
Proof. exact (MK_COMB (@lem5312398 l s c) (@lem5312399 x c)). Qed.
Lemma lem5312401 (l : real) (s : real -> Prop) (x : real -> real) (c : real) : (term220 l s x c) = (term221 l s x c).
Proof. exact (eq_refl (term220 l s x c)). Qed.
Lemma lem5312402 (l : real) (s : real -> Prop) (x : real -> real) (c : real) : (term219 l s x c) = (term221 l s x c).
Proof. exact (TRANS (@lem5312400 l s x c) (@lem5312401 l s x c)). Qed.
Lemma lem5312403 (l : real) (s : real -> Prop) (x : real -> real) : (term222 l s x) = (term223 l s x).
Proof. exact (fun_ext (fun c : real => @lem5312402 l s x c)). Qed.
Lemma lem5312404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312405 (l : real) (s : real -> Prop) (x : real -> real) : (term224 l s x) = (term225 l s x).
Proof. exact (MK_COMB (@lem5312404) (@lem5312403 l s x)). Qed.
Lemma lem5312406 (l : real) (s : real -> Prop) : (term226 l s) = (term227 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5312405 l s x)). Qed.
Lemma lem5312407 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5312408 (l : real) (s : real -> Prop) : (term209 l s) = (term228 l s).
Proof. exact (MK_COMB (@lem5312407) (@lem5312406 l s)). Qed.
Lemma lem5312409 (l : real) (s : real -> Prop) : ((term208 l s) = (term209 l s)) = ((term203 l s) = (term228 l s)).
Proof. exact (MK_COMB (@lem5312397 l s) (@lem5312408 l s)). Qed.
Lemma lem5312410 (l : real) (s : real -> Prop) : (term203 l s) = (term228 l s).
Proof. exact (EQ_MP (@lem5312409 l s) (@lem5312384 l s)). Qed.
Lemma lem5312411 (l : real) (s : real -> Prop) : (term182 l s) = (term228 l s).
Proof. exact (TRANS (@lem5312380 l s) (@lem5312410 l s)). Qed.
Lemma lem5312412 (s : real -> Prop) : (term183 s) = (term229 s).
Proof. exact (fun_ext (fun l : real => @lem5312411 l s)). Qed.
Lemma lem5312413 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312414 (s : real -> Prop) : (term184 s) = (term230 s).
Proof. exact (MK_COMB (@lem5312413) (@lem5312412 s)). Qed.
Lemma lem5312416 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5312417 (P : type1618) : (term231 P) = (term232 P).
Proof. exact (@lem5312416 real (real -> real) P). Qed.
Lemma lem5312418 (s : real -> Prop) : (term233 s) = (term234 s).
Proof. exact (@lem5312417 (term235 s)). Qed.
Lemma lem5312419 (l : real) (s : real -> Prop) : (term236 s l) = (term227 l s).
Proof. exact (eq_refl (term236 s l)). Qed.
Lemma lem5312420 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5312421 (l : real) (s : real -> Prop) (x : real -> real) : (term237 s l x) = (term238 l s x).
Proof. exact (MK_COMB (@lem5312419 l s) (@lem5312420 x)). Qed.
Lemma lem5312422 (l : real) (s : real -> Prop) (x : real -> real) : (term238 l s x) = (term225 l s x).
Proof. exact (eq_refl (term238 l s x)). Qed.
Lemma lem5312423 (l : real) (s : real -> Prop) (x : real -> real) : (term237 s l x) = (term225 l s x).
Proof. exact (TRANS (@lem5312421 l s x) (@lem5312422 l s x)). Qed.
Lemma lem5312424 (l : real) (s : real -> Prop) : (term239 s l) = (term227 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5312423 l s x)). Qed.
Lemma lem5312425 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5312426 (l : real) (s : real -> Prop) : (term240 s l) = (term228 l s).
Proof. exact (MK_COMB (@lem5312425) (@lem5312424 l s)). Qed.
Lemma lem5312427 (s : real -> Prop) : (term241 s) = (term229 s).
Proof. exact (fun_ext (fun l : real => @lem5312426 l s)). Qed.
Lemma lem5312428 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312429 (s : real -> Prop) : (term233 s) = (term230 s).
Proof. exact (MK_COMB (@lem5312428) (@lem5312427 s)). Qed.
Lemma lem5312430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5312431 (s : real -> Prop) : (term242 s) = (term243 s).
Proof. exact (MK_COMB (@lem5312430) (@lem5312429 s)). Qed.
Lemma lem5312432 (l : real) (s : real -> Prop) : (term236 s l) = (term227 l s).
Proof. exact (eq_refl (term236 s l)). Qed.
Lemma lem5312433 (x : type1627) (l : real) : (x l) = (x l).
Proof. exact (eq_refl (x l)). Qed.
Lemma lem5312434 (s : real -> Prop) (x : type1627) (l : real) : (term244 s x l) = (term245 s x l).
Proof. exact (MK_COMB (@lem5312432 l s) (@lem5312433 x l)). Qed.
Lemma lem5312435 (s : real -> Prop) (x : type1627) (l : real) : (term245 s x l) = (term246 s x l).
Proof. exact (eq_refl (term245 s x l)). Qed.
Lemma lem5312436 (s : real -> Prop) (x : type1627) (l : real) : (term244 s x l) = (term246 s x l).
Proof. exact (TRANS (@lem5312434 s x l) (@lem5312435 s x l)). Qed.
Lemma lem5312437 (s : real -> Prop) (x : type1627) : (term247 s x) = (term248 s x).
Proof. exact (fun_ext (fun l : real => @lem5312436 s x l)). Qed.
Lemma lem5312438 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312439 (s : real -> Prop) (x : type1627) : (term249 s x) = (term250 s x).
Proof. exact (MK_COMB (@lem5312438) (@lem5312437 s x)). Qed.
Lemma lem5312440 (s : real -> Prop) : (term251 s) = (term252 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5312439 s x)). Qed.
Lemma lem5312441 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5312442 (s : real -> Prop) : (term234 s) = (term253 s).
Proof. exact (MK_COMB (@lem5312441) (@lem5312440 s)). Qed.
Lemma lem5312443 (s : real -> Prop) : ((term233 s) = (term234 s)) = ((term230 s) = (term253 s)).
Proof. exact (MK_COMB (@lem5312431 s) (@lem5312442 s)). Qed.
Lemma lem5312444 (s : real -> Prop) : (term230 s) = (term253 s).
Proof. exact (EQ_MP (@lem5312443 s) (@lem5312418 s)). Qed.
Lemma lem5312445 (s : real -> Prop) : (term184 s) = (term253 s).
Proof. exact (TRANS (@lem5312414 s) (@lem5312444 s)). Qed.
Lemma lem5312446 : term185 = term254.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312445 s)). Qed.
Lemma lem5312447 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312448 : term186 = term255.
Proof. exact (MK_COMB (@lem5312447) (@lem5312446)). Qed.
Lemma lem5312450 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5312451 (P : type1016) : (term256 P) = (term257 P).
Proof. exact (@lem5312450 (real -> Prop) type1627 P). Qed.
Lemma lem5312452 : term258 = term259.
Proof. exact (@lem5312451 term260). Qed.
Lemma lem5312453 (s : real -> Prop) : (term261 s) = (term252 s).
Proof. exact (eq_refl (term261 s)). Qed.
Lemma lem5312454 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5312455 (s : real -> Prop) (x : type1627) : (term262 s x) = (term263 s x).
Proof. exact (MK_COMB (@lem5312453 s) (@lem5312454 x)). Qed.
Lemma lem5312456 (s : real -> Prop) (x : type1627) : (term263 s x) = (term250 s x).
Proof. exact (eq_refl (term263 s x)). Qed.
Lemma lem5312457 (s : real -> Prop) (x : type1627) : (term262 s x) = (term250 s x).
Proof. exact (TRANS (@lem5312455 s x) (@lem5312456 s x)). Qed.
Lemma lem5312458 (s : real -> Prop) : (term264 s) = (term252 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5312457 s x)). Qed.
Lemma lem5312459 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5312460 (s : real -> Prop) : (term265 s) = (term253 s).
Proof. exact (MK_COMB (@lem5312459) (@lem5312458 s)). Qed.
Lemma lem5312461 : term266 = term254.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312460 s)). Qed.
Lemma lem5312462 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312463 : term258 = term255.
Proof. exact (MK_COMB (@lem5312462) (@lem5312461)). Qed.
Lemma lem5312464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5312465 : term267 = term268.
Proof. exact (MK_COMB (@lem5312464) (@lem5312463)). Qed.
Lemma lem5312466 (s : real -> Prop) : (term261 s) = (term252 s).
Proof. exact (eq_refl (term261 s)). Qed.
Lemma lem5312467 (x : type1019) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5312468 (x : type1019) (s : real -> Prop) : (term269 x s) = (term270 x s).
Proof. exact (MK_COMB (@lem5312466 s) (@lem5312467 x s)). Qed.
Lemma lem5312469 (x : type1019) (s : real -> Prop) : (term270 x s) = (term271 x s).
Proof. exact (eq_refl (term270 x s)). Qed.
Lemma lem5312470 (x : type1019) (s : real -> Prop) : (term269 x s) = (term271 x s).
Proof. exact (TRANS (@lem5312468 x s) (@lem5312469 x s)). Qed.
Lemma lem5312471 (x : type1019) : (term272 x) = (term273 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312470 x s)). Qed.
Lemma lem5312472 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312473 (x : type1019) : (term274 x) = (term275 x).
Proof. exact (MK_COMB (@lem5312472) (@lem5312471 x)). Qed.
Lemma lem5312474 : term276 = term277.
Proof. exact (fun_ext (fun x : type1019 => @lem5312473 x)). Qed.
Lemma lem5312475 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5312476 : term259 = term278.
Proof. exact (MK_COMB (@lem5312475) (@lem5312474)). Qed.
Lemma lem5312477 : (term258 = term259) = (term255 = term278).
Proof. exact (MK_COMB (@lem5312465) (@lem5312476)). Qed.
Lemma lem5312478 : term255 = term278.
Proof. exact (EQ_MP (@lem5312477) (@lem5312452)). Qed.
Lemma lem5312480 : term186 = term278.
Proof. exact (TRANS (@lem5312448) (@lem5312478)). Qed.
Lemma lem5312481 : term127 = term278.
Proof. exact (TRANS (@lem5312252) (@lem5312480)). Qed.
Lemma lem5312482 (h1 : term127) : term278.
Proof. exact (EQ_MP (@lem5312481) (@lem5312083 h1)). Qed.
Lemma lem5312483 (x : type1019) (h1 : term275 x) : term275 x.
Proof. exact (h1). Qed.
Lemma lem5312484 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term166 l s c.
Proof. exact (h1). Qed.
Lemma lem5312490 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5312535 (x : type1019) (s : real -> Prop) (l : real) (c : real) : (term279 x s l c) = (term279 x s l c).
Proof. exact (eq_refl (term279 x s l c)). Qed.
Lemma lem5312536 (x : type1019) (s : real -> Prop) (l : real) : (term280 x s l) = (term280 x s l).
Proof. exact (fun_ext (fun c : real => @lem5312535 x s l c)). Qed.
Lemma lem5312537 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312538 (x : type1019) (s : real -> Prop) (l : real) : (term281 x s l) = (term281 x s l).
Proof. exact (MK_COMB (@lem5312537) (@lem5312536 x s l)). Qed.
Lemma lem5312539 (x : type1019) (s : real -> Prop) : (term282 x s) = (term282 x s).
Proof. exact (fun_ext (fun l : real => @lem5312538 x s l)). Qed.
Lemma lem5312540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312541 (x : type1019) (s : real -> Prop) : (term271 x s) = (term271 x s).
Proof. exact (MK_COMB (@lem5312540) (@lem5312539 x s)). Qed.
Lemma lem5312542 (x : type1019) : (term273 x) = (term273 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312541 x s)). Qed.
Lemma lem5312543 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312544 (x : type1019) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5312543) (@lem5312542 x)). Qed.
Lemma lem5312545 (x : type1019) (h1 : term275 x) : term275 x.
Proof. exact (EQ_MP (@lem5312544 x) (@lem5312483 x h1)). Qed.
Lemma lem5312562 (s : real -> Prop) (x : real) (c : real) : (term154 s x c) = (term154 s x c).
Proof. exact (eq_refl (term154 s x c)). Qed.
Lemma lem5312563 (s : real -> Prop) (c : real) : (term162 s c) = (term162 s c).
Proof. exact (fun_ext (fun x : real => @lem5312562 s x c)). Qed.
Lemma lem5312564 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312565 (s : real -> Prop) (c : real) : (term163 s c) = (term163 s c).
Proof. exact (MK_COMB (@lem5312564) (@lem5312563 s c)). Qed.
Lemma lem5312572 (l : real) (c : real) : (term164 l c) = (term164 l c).
Proof. exact (eq_refl (term164 l c)). Qed.
Lemma lem5312573 (l : real) (s : real -> Prop) (c : real) : (term166 l s c) = (term166 l s c).
Proof. exact (MK_COMB (@lem5312572 l c) (@lem5312565 s c)). Qed.
Lemma lem5312574 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term166 l s c.
Proof. exact (EQ_MP (@lem5312573 l s c) (@lem5312484 l s c h1)). Qed.
Lemma lem5312575 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term163 s c.
Proof. exact (proj2 (@lem5312574 l s c h1)). Qed.
Lemma lem5312580 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5312604 (x : type1019) (s : real -> Prop) (l : real) (c : real) : (term279 x s l c) = (term283 x s l c).
Proof. exact (@lem19490 (term284 x l c s) (term175 s l c) (term285 x s l c)). Qed.
Lemma lem5312605 (x : type1019) (s : real -> Prop) (l : real) : (term280 x s l) = (term286 x s l).
Proof. exact (fun_ext (fun c : real => @lem5312604 x s l c)). Qed.
Lemma lem5312606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312607 (x : type1019) (s : real -> Prop) (l : real) : (term281 x s l) = (term287 x s l).
Proof. exact (MK_COMB (@lem5312606) (@lem5312605 x s l)). Qed.
Lemma lem5312608 (x : type1019) (s : real -> Prop) : (term282 x s) = (term288 x s).
Proof. exact (fun_ext (fun l : real => @lem5312607 x s l)). Qed.
Lemma lem5312609 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312610 (x : type1019) (s : real -> Prop) : (term271 x s) = (term289 x s).
Proof. exact (MK_COMB (@lem5312609) (@lem5312608 x s)). Qed.
Lemma lem5312611 (x : type1019) : (term273 x) = (term290 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5312610 x s)). Qed.
Lemma lem5312612 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5312614 (x : type1019) : (term275 x) = (term291 x).
Proof. exact (MK_COMB (@lem5312612) (@lem5312611 x)). Qed.
Lemma lem5312615 (x : type1019) (h1 : term275 x) : term291 x.
Proof. exact (EQ_MP (@lem5312614 x) (@lem5312545 x h1)). Qed.
Lemma lem5312627 (s : real -> Prop) (x : real) (c : real) : (term154 s x c) = (term154 s x c).
Proof. exact (eq_refl (term154 s x c)). Qed.
Lemma lem5312628 (s : real -> Prop) (c : real) : (term162 s c) = (term162 s c).
Proof. exact (fun_ext (fun x : real => @lem5312627 s x c)). Qed.
Lemma lem5312629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5312631 (s : real -> Prop) (c : real) : (term163 s c) = (term163 s c).
Proof. exact (MK_COMB (@lem5312629) (@lem5312628 s c)). Qed.
Lemma lem5312632 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term163 s c.
Proof. exact (EQ_MP (@lem5312631 s c) (@lem5312575 l s c h1)). Qed.
Lemma lem5312633 (_69677 : real -> Prop) (x : type1019) (h1 : term275 x) : term292 x _69677.
Proof. exact (@lem5312615 x h1 _69677). Qed.
Lemma lem5312634 (x : type1019) (_69677 : real -> Prop) : (term292 x _69677) = (term289 x _69677).
Proof. exact (eq_refl (term292 x _69677)). Qed.
Lemma lem5312635 (_69677 : real -> Prop) (x : type1019) (h1 : term275 x) : term289 x _69677.
Proof. exact (EQ_MP (@lem5312634 x _69677) (@lem5312633 _69677 x h1)). Qed.
Lemma lem5312636 (_69677 : real -> Prop) (_69678 : real) (x : type1019) (h1 : term275 x) : term293 x _69677 _69678.
Proof. exact (@lem5312635 _69677 x h1 _69678). Qed.
Lemma lem5312637 (x : type1019) (_69677 : real -> Prop) (_69678 : real) : (term293 x _69677 _69678) = (term287 x _69677 _69678).
Proof. exact (eq_refl (term293 x _69677 _69678)). Qed.
Lemma lem5312638 (_69677 : real -> Prop) (_69678 : real) (x : type1019) (h1 : term275 x) : term287 x _69677 _69678.
Proof. exact (EQ_MP (@lem5312637 x _69677 _69678) (@lem5312636 _69677 _69678 x h1)). Qed.
Lemma lem5312639 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term294 x _69677 _69678 _69679.
Proof. exact (@lem5312638 _69677 _69678 x h1 _69679). Qed.
Lemma lem5312640 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term294 x _69677 _69678 _69679) = (term283 x _69677 _69678 _69679).
Proof. exact (eq_refl (term294 x _69677 _69678 _69679)). Qed.
Lemma lem5312641 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term283 x _69677 _69678 _69679.
Proof. exact (EQ_MP (@lem5312640 x _69677 _69678 _69679) (@lem5312639 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312642 (_69680 : real) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term295 s c _69680.
Proof. exact (@lem5312632 l s c h1 _69680). Qed.
Lemma lem5312643 (s : real -> Prop) (_69680 : real) (c : real) : (term295 s c _69680) = (term154 s _69680 c).
Proof. exact (eq_refl (term295 s c _69680)). Qed.
Lemma lem5312645 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term296 x _69677 _69678 _69679.
Proof. exact (proj2 (@lem5312641 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312646 (_69678 : real) (_69679 : real) (_69677 : real -> Prop) (x : type1019) (h1 : term275 x) : term297 x _69678 _69679 _69677.
Proof. exact (proj1 (@lem5312641 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312648 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5312656 (_69680 : real) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term154 s _69680 c.
Proof. exact (EQ_MP (@lem5312643 s _69680 c) (@lem5312642 _69680 l s c h1)). Qed.
Lemma lem5312667 (x : type1019) (_69678 : real) (_69679 : real) (_69677 : real -> Prop) : (term297 x _69678 _69679 _69677) = (term298 x _69678 _69679 _69677).
Proof. exact (@lem5311044 (term83 _69677 _69678) (term0 _69678 _69679) (term284 x _69678 _69679 _69677)). Qed.
Lemma lem5312668 (_69678 : real) (_69679 : real) (_69677 : real -> Prop) (x : type1019) (h1 : term275 x) : term298 x _69678 _69679 _69677.
Proof. exact (EQ_MP (@lem5312667 x _69678 _69679 _69677) (@lem5312646 _69678 _69679 _69677 x h1)). Qed.
Lemma lem5312679 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term296 x _69677 _69678 _69679) = (term299 x _69677 _69678 _69679).
Proof. exact (@lem5311044 (term83 _69677 _69678) (term0 _69678 _69679) (term285 x _69677 _69678 _69679)). Qed.
Lemma lem5312680 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term299 x _69677 _69678 _69679.
Proof. exact (EQ_MP (@lem5312679 x _69677 _69678 _69679) (@lem5312645 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312682 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5312683 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term86 s l.
Proof. exact (fun h0 : term83 s l => @lem5312682 s l h1). Qed.
Lemma lem5312685 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312686 (s : real -> Prop) (l : real) : (term86 s l) = (has_inf s l).
Proof. exact (@lem5312685 (has_inf s l)). Qed.
Lemma lem5312687 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (EQ_MP (@lem5312686 s l) (@lem5312683 s l h1)). Qed.
Lemma lem5312689 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt l c.
Proof. exact (proj1 (@lem5312574 l s c h1)). Qed.
Lemma lem5312690 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term300 l c.
Proof. exact (fun h0 : term0 l c => @lem5312689 l s c h1). Qed.
Lemma lem5312692 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312693 (l : real) (c : real) : (term300 l c) = (real_lt l c).
Proof. exact (@lem5312692 (real_lt l c)). Qed.
Lemma lem5312694 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt l c.
Proof. exact (EQ_MP (@lem5312693 l c) (@lem5312690 l s c h1)). Qed.
Lemma lem5312710 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5312711 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term301 x _69678 _69679 _69677) = (term302 x _69677 _69678 _69679).
Proof. exact (@lem5312710 (term284 x _69678 _69679 _69677) (term0 _69678 _69679)). Qed.
Lemma lem5312717 (_69677 : real -> Prop) (_69678 : real) : (term303 _69677 _69678) = (term303 _69677 _69678).
Proof. exact (eq_refl (term303 _69677 _69678)). Qed.
Lemma lem5312718 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term298 x _69678 _69679 _69677) = (term304 x _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312717 _69677 _69678) (@lem5312711 x _69677 _69678 _69679)). Qed.
Lemma lem5312722 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5312723 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term304 x _69677 _69678 _69679) = (term305 x _69677 _69678 _69679).
Proof. exact (@lem5312722 (term284 x _69678 _69679 _69677) (term83 _69677 _69678) (term0 _69678 _69679)). Qed.
Lemma lem5312739 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term298 x _69678 _69679 _69677) = (term305 x _69677 _69678 _69679).
Proof. exact (TRANS (@lem5312718 x _69677 _69678 _69679) (@lem5312723 x _69677 _69678 _69679)). Qed.
Lemma lem5312740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5312741 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term306 x _69678 _69679 _69677) = (term307 x _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312740) (@lem5312739 x _69677 _69678 _69679)). Qed.
Lemma lem5312757 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term305 x _69677 _69678 _69679) = (term305 x _69677 _69678 _69679).
Proof. exact (eq_refl (term305 x _69677 _69678 _69679)). Qed.
Lemma lem5312758 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : ((term298 x _69678 _69679 _69677) = (term305 x _69677 _69678 _69679)) = ((term305 x _69677 _69678 _69679) = (term305 x _69677 _69678 _69679)).
Proof. exact (MK_COMB (@lem5312741 x _69677 _69678 _69679) (@lem5312757 x _69677 _69678 _69679)). Qed.
Lemma lem5312760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5312761 (x : Prop) : (x = x) = True.
Proof. exact (@lem5312760 Prop x). Qed.
Lemma lem5312762 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : ((term305 x _69677 _69678 _69679) = (term305 x _69677 _69678 _69679)) = True.
Proof. exact (@lem5312761 (term305 x _69677 _69678 _69679)). Qed.
Lemma lem5312763 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : ((term298 x _69678 _69679 _69677) = (term305 x _69677 _69678 _69679)) = True.
Proof. exact (TRANS (@lem5312758 x _69677 _69678 _69679) (@lem5312762 x _69677 _69678 _69679)). Qed.
Lemma lem5312764 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : True = ((term298 x _69678 _69679 _69677) = (term305 x _69677 _69678 _69679)).
Proof. exact (SYM (@lem5312763 x _69677 _69678 _69679)). Qed.
Lemma lem5312765 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term298 x _69678 _69679 _69677) = (term305 x _69677 _69678 _69679).
Proof. exact (EQ_MP (@lem5312764 x _69677 _69678 _69679) (@lem0)). Qed.
Lemma lem5312766 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term305 x _69677 _69678 _69679.
Proof. exact (EQ_MP (@lem5312765 x _69677 _69678 _69679) (@lem5312668 _69678 _69679 _69677 x h1)). Qed.
Lemma lem5312768 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5312769 (x : type1019) (_69678 : real) (_69679 : real) (_69677 : real -> Prop) : (term305 x _69677 _69678 _69679) = (term308 x _69678 _69679 _69677).
Proof. exact (@lem5312768 (term175 _69677 _69678 _69679) (term284 x _69678 _69679 _69677)). Qed.
Lemma lem5312771 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5312772 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term309 _69677 _69678 _69679) = (term310 _69677 _69678 _69679).
Proof. exact (@lem5312771 (term83 _69677 _69678) (term0 _69678 _69679)). Qed.
Lemma lem5312774 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5312775 (_69677 : real -> Prop) (_69678 : real) : (term107 _69677 _69678) = (has_inf _69677 _69678).
Proof. exact (@lem5312774 (has_inf _69677 _69678)). Qed.
Lemma lem5312776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5312777 (_69677 : real -> Prop) (_69678 : real) : (term108 _69677 _69678) = (term109 _69677 _69678).
Proof. exact (MK_COMB (@lem5312776) (@lem5312775 _69677 _69678)). Qed.
Lemma lem5312779 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5312780 (_69678 : real) (_69679 : real) : (term311 _69678 _69679) = (real_lt _69678 _69679).
Proof. exact (@lem5312779 (real_lt _69678 _69679)). Qed.
Lemma lem5312781 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term310 _69677 _69678 _69679) = (term180 _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312777 _69677 _69678) (@lem5312780 _69678 _69679)). Qed.
Lemma lem5312782 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term309 _69677 _69678 _69679) = (term180 _69677 _69678 _69679).
Proof. exact (TRANS (@lem5312772 _69677 _69678 _69679) (@lem5312781 _69677 _69678 _69679)). Qed.
Lemma lem5312783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5312784 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term312 _69677 _69678 _69679) = (term143 _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312783) (@lem5312782 _69677 _69678 _69679)). Qed.
Lemma lem5312785 (x : type1019) (_69678 : real) (_69679 : real) (_69677 : real -> Prop) : (term284 x _69678 _69679 _69677) = (term284 x _69678 _69679 _69677).
Proof. exact (eq_refl (term284 x _69678 _69679 _69677)). Qed.
Lemma lem5312786 (x : type1019) (_69678 : real) (_69679 : real) (_69677 : real -> Prop) : (term308 x _69678 _69679 _69677) = (term313 x _69678 _69679 _69677).
Proof. exact (MK_COMB (@lem5312784 _69677 _69678 _69679) (@lem5312785 x _69678 _69679 _69677)). Qed.
Lemma lem5312787 (x : type1019) (_69678 : real) (_69679 : real) (_69677 : real -> Prop) : (term305 x _69677 _69678 _69679) = (term313 x _69678 _69679 _69677).
Proof. exact (TRANS (@lem5312769 x _69678 _69679 _69677) (@lem5312786 x _69678 _69679 _69677)). Qed.
Lemma lem5312789 (c : real) (s : real -> Prop) (l : real) (h1 : term166 l s c) (h2 : has_inf s l) : term180 s l c.
Proof. exact (conj (@lem5312687 s l h2) (@lem5312694 l s c h1)). Qed.
Lemma lem5312791 (_69678 : real) (_69679 : real) (_69677 : real -> Prop) (x : type1019) (h1 : term275 x) : term313 x _69678 _69679 _69677.
Proof. exact (EQ_MP (@lem5312787 x _69678 _69679 _69677) (@lem5312766 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312792 (l : real) (c : real) (s : real -> Prop) (x : type1019) (h1 : term275 x) : term313 x l c s.
Proof. exact (@lem5312791 l c s x h1). Qed.
Lemma lem5312795 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term284 x l c s.
Proof. exact (@lem5312792 l c s x h1 (@lem5312789 c s l h2 h3)). Qed.
Lemma lem5312796 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term314 x l c s.
Proof. exact (fun h0 : term315 x l c s => @lem5312795 x c s l h1 h2 h3). Qed.
Lemma lem5312798 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312799 (x : type1019) (l : real) (c : real) (s : real -> Prop) : (term314 x l c s) = (term284 x l c s).
Proof. exact (@lem5312798 (term284 x l c s)). Qed.
Lemma lem5312800 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term284 x l c s.
Proof. exact (EQ_MP (@lem5312799 x l c s) (@lem5312796 x c s l h1 h2 h3)). Qed.
Lemma lem5312802 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5312803 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term86 s l.
Proof. exact (fun h0 : term83 s l => @lem5312802 s l h1). Qed.
Lemma lem5312805 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312806 (s : real -> Prop) (l : real) : (term86 s l) = (has_inf s l).
Proof. exact (@lem5312805 (has_inf s l)). Qed.
Lemma lem5312807 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (EQ_MP (@lem5312806 s l) (@lem5312803 s l h1)). Qed.
Lemma lem5312809 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt l c.
Proof. exact (proj1 (@lem5312574 l s c h1)). Qed.
Lemma lem5312810 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term300 l c.
Proof. exact (fun h0 : term0 l c => @lem5312809 l s c h1). Qed.
Lemma lem5312812 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312813 (l : real) (c : real) : (term300 l c) = (real_lt l c).
Proof. exact (@lem5312812 (real_lt l c)). Qed.
Lemma lem5312814 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt l c.
Proof. exact (EQ_MP (@lem5312813 l c) (@lem5312810 l s c h1)). Qed.
Lemma lem5312830 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5312831 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term316 x _69677 _69678 _69679) = (term317 x _69677 _69678 _69679).
Proof. exact (@lem5312830 (term285 x _69677 _69678 _69679) (term0 _69678 _69679)). Qed.
Lemma lem5312837 (_69677 : real -> Prop) (_69678 : real) : (term303 _69677 _69678) = (term303 _69677 _69678).
Proof. exact (eq_refl (term303 _69677 _69678)). Qed.
Lemma lem5312838 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term299 x _69677 _69678 _69679) = (term318 x _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312837 _69677 _69678) (@lem5312831 x _69677 _69678 _69679)). Qed.
Lemma lem5312842 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5312843 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term318 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679).
Proof. exact (@lem5312842 (term285 x _69677 _69678 _69679) (term83 _69677 _69678) (term0 _69678 _69679)). Qed.
Lemma lem5312859 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term299 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679).
Proof. exact (TRANS (@lem5312838 x _69677 _69678 _69679) (@lem5312843 x _69677 _69678 _69679)). Qed.
Lemma lem5312860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5312861 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term320 x _69677 _69678 _69679) = (term321 x _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312860) (@lem5312859 x _69677 _69678 _69679)). Qed.
Lemma lem5312877 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term319 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679).
Proof. exact (eq_refl (term319 x _69677 _69678 _69679)). Qed.
Lemma lem5312878 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : ((term299 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679)) = ((term319 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679)).
Proof. exact (MK_COMB (@lem5312861 x _69677 _69678 _69679) (@lem5312877 x _69677 _69678 _69679)). Qed.
Lemma lem5312880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5312881 (x : Prop) : (x = x) = True.
Proof. exact (@lem5312880 Prop x). Qed.
Lemma lem5312882 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : ((term319 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679)) = True.
Proof. exact (@lem5312881 (term319 x _69677 _69678 _69679)). Qed.
Lemma lem5312883 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : ((term299 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679)) = True.
Proof. exact (TRANS (@lem5312878 x _69677 _69678 _69679) (@lem5312882 x _69677 _69678 _69679)). Qed.
Lemma lem5312884 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : True = ((term299 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679)).
Proof. exact (SYM (@lem5312883 x _69677 _69678 _69679)). Qed.
Lemma lem5312885 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term299 x _69677 _69678 _69679) = (term319 x _69677 _69678 _69679).
Proof. exact (EQ_MP (@lem5312884 x _69677 _69678 _69679) (@lem0)). Qed.
Lemma lem5312886 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term319 x _69677 _69678 _69679.
Proof. exact (EQ_MP (@lem5312885 x _69677 _69678 _69679) (@lem5312680 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312888 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5312889 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term319 x _69677 _69678 _69679) = (term322 x _69677 _69678 _69679).
Proof. exact (@lem5312888 (term175 _69677 _69678 _69679) (term285 x _69677 _69678 _69679)). Qed.
Lemma lem5312891 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5312892 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term309 _69677 _69678 _69679) = (term310 _69677 _69678 _69679).
Proof. exact (@lem5312891 (term83 _69677 _69678) (term0 _69678 _69679)). Qed.
Lemma lem5312894 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5312895 (_69677 : real -> Prop) (_69678 : real) : (term107 _69677 _69678) = (has_inf _69677 _69678).
Proof. exact (@lem5312894 (has_inf _69677 _69678)). Qed.
Lemma lem5312896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5312897 (_69677 : real -> Prop) (_69678 : real) : (term108 _69677 _69678) = (term109 _69677 _69678).
Proof. exact (MK_COMB (@lem5312896) (@lem5312895 _69677 _69678)). Qed.
Lemma lem5312899 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5312900 (_69678 : real) (_69679 : real) : (term311 _69678 _69679) = (real_lt _69678 _69679).
Proof. exact (@lem5312899 (real_lt _69678 _69679)). Qed.
Lemma lem5312901 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term310 _69677 _69678 _69679) = (term180 _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312897 _69677 _69678) (@lem5312900 _69678 _69679)). Qed.
Lemma lem5312902 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term309 _69677 _69678 _69679) = (term180 _69677 _69678 _69679).
Proof. exact (TRANS (@lem5312892 _69677 _69678 _69679) (@lem5312901 _69677 _69678 _69679)). Qed.
Lemma lem5312903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5312904 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term312 _69677 _69678 _69679) = (term143 _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312903) (@lem5312902 _69677 _69678 _69679)). Qed.
Lemma lem5312905 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term285 x _69677 _69678 _69679) = (term285 x _69677 _69678 _69679).
Proof. exact (eq_refl (term285 x _69677 _69678 _69679)). Qed.
Lemma lem5312906 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term322 x _69677 _69678 _69679) = (term323 x _69677 _69678 _69679).
Proof. exact (MK_COMB (@lem5312904 _69677 _69678 _69679) (@lem5312905 x _69677 _69678 _69679)). Qed.
Lemma lem5312907 (x : type1019) (_69677 : real -> Prop) (_69678 : real) (_69679 : real) : (term319 x _69677 _69678 _69679) = (term323 x _69677 _69678 _69679).
Proof. exact (TRANS (@lem5312889 x _69677 _69678 _69679) (@lem5312906 x _69677 _69678 _69679)). Qed.
Lemma lem5312909 (c : real) (s : real -> Prop) (l : real) (h1 : term166 l s c) (h2 : has_inf s l) : term180 s l c.
Proof. exact (conj (@lem5312807 s l h2) (@lem5312814 l s c h1)). Qed.
Lemma lem5312911 (_69677 : real -> Prop) (_69678 : real) (_69679 : real) (x : type1019) (h1 : term275 x) : term323 x _69677 _69678 _69679.
Proof. exact (EQ_MP (@lem5312907 x _69677 _69678 _69679) (@lem5312886 _69677 _69678 _69679 x h1)). Qed.
Lemma lem5312912 (s : real -> Prop) (l : real) (c : real) (x : type1019) (h1 : term275 x) : term323 x s l c.
Proof. exact (@lem5312911 s l c x h1). Qed.
Lemma lem5312915 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term285 x s l c.
Proof. exact (@lem5312912 s l c x h1 (@lem5312909 c s l h2 h3)). Qed.
Lemma lem5312916 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term324 x s l c.
Proof. exact (fun h0 : term325 x s l c => @lem5312915 x c s l h1 h2 h3). Qed.
Lemma lem5312918 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312919 (x : type1019) (s : real -> Prop) (l : real) (c : real) : (term324 x s l c) = (term285 x s l c).
Proof. exact (@lem5312918 (term285 x s l c)). Qed.
Lemma lem5312920 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term285 x s l c.
Proof. exact (EQ_MP (@lem5312919 x s l c) (@lem5312916 x c s l h1 h2 h3)). Qed.
Lemma lem5312922 (a : Prop) (b : Prop) : (term326 a b) = (term327 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5312923 (s : real -> Prop) (_69680 : real) (c : real) : (term154 s _69680 c) = (term153 s _69680 c).
Proof. exact (@lem5312922 (@IN real _69680 s) (real_lt _69680 c)). Qed.
Lemma lem5312925 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5312926 (s : real -> Prop) (_69680 : real) (c : real) : (term153 s _69680 c) = (term328 s _69680 c).
Proof. exact (@lem5312925 (term140 s _69680 c)). Qed.
Lemma lem5312927 (s : real -> Prop) (_69680 : real) (c : real) : (term154 s _69680 c) = (term328 s _69680 c).
Proof. exact (TRANS (@lem5312923 s _69680 c) (@lem5312926 s _69680 c)). Qed.
Lemma lem5312929 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term329 x s l c.
Proof. exact (conj (@lem5312800 x c s l h1 h2 h3) (@lem5312920 x c s l h1 h2 h3)). Qed.
Lemma lem5312931 (_69680 : real) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term328 s _69680 c.
Proof. exact (EQ_MP (@lem5312927 s _69680 c) (@lem5312656 _69680 l s c h1)). Qed.
Lemma lem5312932 (x : type1019) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term330 x s l c.
Proof. exact (@lem5312931 (x s l c) l s c h1). Qed.
Lemma lem5312935 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (@lem5312932 x l s c h2 (@lem5312929 x c s l h1 h2 h3)). Qed.
Lemma lem5312936 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : term115.
Proof. exact (fun h0 : ~ False => @lem5312935 x c s l h1 h2 h3). Qed.
Lemma lem5312938 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5312939 : term115 = False.
Proof. exact (@lem5312938 False). Qed.
Lemma lem5312940 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312939) (@lem5312936 x c s l h1 h2 h3)). Qed.
Lemma lem5312941 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5312940 x c s l h1 h2 h3) (fun h4 : False => @lem5312648 s l h3)). Qed.
Lemma lem5312942 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312941 x c s l h1 h2 h3) (@lem5312648 s l h3)). Qed.
Lemma lem5312943 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5312942 x c s l h1 h2 h3) (fun h4 : False => @lem5312580 s l h3)). Qed.
Lemma lem5312944 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312943 x c s l h1 h2 h3) (@lem5312580 s l h3)). Qed.
Lemma lem5312945 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5312944 x c s l h1 h2 h3) (fun h4 : False => @lem5312580 s l h3)). Qed.
Lemma lem5312946 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312945 x c s l h1 h2 h3) (@lem5312580 s l h3)). Qed.
Lemma lem5312947 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : (term166 l s c) = False.
Proof. exact (prop_ext (fun h4 : term166 l s c => @lem5312946 x c s l h1 h2 h3) (fun h4 : False => @lem5312574 l s c h2)). Qed.
Lemma lem5312948 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312947 x c s l h1 h2 h3) (@lem5312574 l s c h2)). Qed.
Lemma lem5312949 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : (term275 x) = False.
Proof. exact (prop_ext (fun h4 : term275 x => @lem5312948 x c s l h1 h2 h3) (fun h4 : False => @lem5312545 x h1)). Qed.
Lemma lem5312950 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312949 x c s l h1 h2 h3) (@lem5312545 x h1)). Qed.
Lemma lem5312951 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5312950 x c s l h1 h2 h3) (fun h4 : False => @lem5312490 s l h3)). Qed.
Lemma lem5312952 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312951 x c s l h1 h2 h3) (@lem5312490 s l h3)). Qed.
Lemma lem5312953 (x : type1019) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term120 l s) (h3 : has_inf s l) : False.
Proof. exact (ex_elim (@lem5312223 l s h2) (fun c : real => fun h0 : term172 l s c => @lem5312952 x c s l h1 h0 h3)). Qed.
Lemma lem5312954 (s : real -> Prop) (l : real) (h1 : term127) (h2 : term120 l s) (h3 : has_inf s l) : False.
Proof. exact (ex_elim (@lem5312482 h1) (fun x : type1019 => fun h0 : term277 x => @lem5312953 x s l h0 h2 h3)). Qed.
Lemma lem5312955 (s : real -> Prop) (l : real) (h1 : term127) (h2 : term120 l s) (h3 : has_inf s l) : (has_inf s l) = False.
Proof. exact (prop_ext (fun h4 : has_inf s l => @lem5312954 s l h1 h2 h3) (fun h4 : False => @lem5312089 s l h3)). Qed.
Lemma lem5312956 (s : real -> Prop) (l : real) (h1 : term127) (h2 : term120 l s) (h3 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312955 s l h1 h2 h3) (@lem5312089 s l h3)). Qed.
Lemma lem5312957 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_inf s l) : term125.
Proof. exact (fun h0 : term127 => @lem5312956 s l h0 h1 h2). Qed.
Lemma lem5312958 : term125 = term126.
Proof. exact (@lem69 term127). Qed.
Lemma lem5312959 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_inf s l) : term126.
Proof. exact (EQ_MP (@lem5312958) (@lem5312957 s l h1 h2)). Qed.
Lemma lem5312960 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term130 l s.
Proof. exact (fun h0 : term120 l s => @lem5312959 s l h0 h1). Qed.
Lemma lem5312961 (l : real) (s : real -> Prop) : term131 l s.
Proof. exact (fun h0 : has_inf s l => @lem5312960 s l h0). Qed.
Lemma lem5312966 (s : real -> Prop) : term135 s.
Proof. exact (fun l : real => @lem5312961 l s). Qed.
Lemma lem5312971 : term139.
Proof. exact (fun s : real -> Prop => @lem5312966 s). Qed.
Lemma lem5312972 : term138.
Proof. exact (EQ_MP (@lem5312080) (@lem5312971)). Qed.
Lemma lem5312973 (s : real -> Prop) : term331 s.
Proof. exact (@lem5312972 s). Qed.
Lemma lem5312974 (s : real -> Prop) : (term331 s) = (term134 s).
Proof. exact (eq_refl (term331 s)). Qed.
Lemma lem5312975 (s : real -> Prop) : term134 s.
Proof. exact (EQ_MP (@lem5312974 s) (@lem5312973 s)). Qed.
Lemma lem5312976 (s : real -> Prop) (l : real) : term332 s l.
Proof. exact (@lem5312975 s l). Qed.
Lemma lem5312977 (l : real) (s : real -> Prop) : (term332 s l) = (term121 l s).
Proof. exact (eq_refl (term332 s l)). Qed.
Lemma lem5312978 (l : real) (s : real -> Prop) : term121 l s.
Proof. exact (EQ_MP (@lem5312977 l s) (@lem5312976 s l)). Qed.
Lemma lem5312980 (l : real) (s : real -> Prop) : term121 l s.
Proof. exact (@lem5311794 l s (@lem5312978 l s)). Qed.
Lemma lem5312981 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term129 l s.
Proof. exact (@lem5312980 l s (@lem5311061 s l h1)). Qed.
Lemma lem5312982 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_inf s l) : term125.
Proof. exact (@lem5312981 s l h2 (@lem5311779 l s h1)). Qed.
Lemma lem5312983 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_inf s l) : False.
Proof. exact (@lem5312982 s l h1 h2 (@lem5308185)). Qed.
Lemma lem5312984 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_inf s l) : (term120 l s) = False.
Proof. exact (prop_ext (fun h3 : term120 l s => @lem5312983 s l h1 h2) (fun h3 : False => @lem5311779 l s h1)). Qed.
Lemma lem5312985 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_inf s l) : False.
Proof. exact (EQ_MP (@lem5312984 s l h1 h2) (@lem5311779 l s h1)). Qed.
Lemma lem5312986 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term119 l s.
Proof. exact (fun h0 : term120 l s => @lem5312985 s l h0 h1). Qed.
Lemma lem5312987 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term118 l s.
Proof. exact (EQ_MP (@lem5311778 l s) (@lem5312986 s l h1)). Qed.
Lemma lem5312988 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term333 l s.
Proof. exact (conj (@lem5311774 s l h1) (@lem5312987 s l h1)). Qed.
Lemma lem5312989 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term334 l s.
Proof. exact (conj (@lem5311110 s l h1) (@lem5312988 s l h1)). Qed.
Lemma lem5312990 (s : real -> Prop) (l : real) (h1 : has_inf s l) : (has_inf s l) = (term334 l s).
Proof. exact (prop_ext (fun h2 : has_inf s l => @lem5312989 s l h1) (fun h2 : term334 l s => @lem5311061 s l h1)). Qed.
Lemma lem5312991 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term334 l s.
Proof. exact (EQ_MP (@lem5312990 s l h1) (@lem5311061 s l h1)). Qed.
Lemma lem5312992 (l : real) (s : real -> Prop) : term335 l s.
Proof. exact (fun h0 : has_inf s l => @lem5312991 s l h0). Qed.
Lemma lem5312993 (l : real) (s : real -> Prop) (h1 : term334 l s) : term334 l s.
Proof. exact (h1). Qed.
Lemma lem5312994 (l : real) (s : real -> Prop) (h1 : term333 l s) : term333 l s.
Proof. exact (h1). Qed.
Lemma lem5312995 (s : real -> Prop) (h1 : term22 s) : term22 s.
Proof. exact (h1). Qed.
Lemma lem5312996 (l : real) (s : real -> Prop) (h1 : term118 l s) : term118 l s.
Proof. exact (h1). Qed.
Lemma lem5312997 (s : real -> Prop) (l : real) (h1 : term25 s l) : term25 s l.
Proof. exact (h1). Qed.
Lemma lem5312998 (s : real -> Prop) : term336 s.
Proof. exact (@lem5289985 s). Qed.
Lemma lem5312999 (s : real -> Prop) : (term336 s) = (term337 s).
Proof. exact (eq_refl (term336 s)). Qed.
Lemma lem5313000 (s : real -> Prop) : term337 s.
Proof. exact (EQ_MP (@lem5312999 s) (@lem5312998 s)). Qed.
Lemma lem5313001 (s : real -> Prop) (b : real) : term338 s b.
Proof. exact (@lem5313000 s b). Qed.
Lemma lem5313002 (s : real -> Prop) (b : real) : (term338 s b) = ((has_inf s b) = (term339 s b)).
Proof. exact (eq_refl (term338 s b)). Qed.
Lemma lem5313028 (s : real -> Prop) (b : real) : (has_inf s b) = (term339 s b).
Proof. exact (EQ_MP (@lem5313002 s b) (@lem5313001 s b)). Qed.
Lemma lem5313029 (s : real -> Prop) (l : real) : (has_inf s l) = (term339 s l).
Proof. exact (@lem5313028 s l). Qed.
Lemma lem5313042 (s : real -> Prop) (l : real) : (term339 s l) = (has_inf s l).
Proof. exact (SYM (@lem5313029 s l)). Qed.
Lemma lem5313043 (s : real -> Prop) (c : real) (h1 : term25 s c) : term25 s c.
Proof. exact (h1). Qed.
Lemma lem5313045 (x : real) (y : real) : (real_le y x) = (term0 x y).
Proof. exact (EQ_MP (@lem5311033 x y) (@lem5311032 x y)). Qed.
Lemma lem5313046 (l : real) (c : real) : (real_le c l) = (term0 l c).
Proof. exact (@lem5313045 l c). Qed.
Lemma lem5313047 (c : real) (l : real) : (term0 l c) = (real_le c l).
Proof. exact (SYM (@lem5313046 l c)). Qed.
Lemma lem5313048 (l : real) (c : real) (h1 : real_lt l c) : real_lt l c.
Proof. exact (h1). Qed.
Lemma lem5313049 (c : real) (l : real) (s : real -> Prop) (h1 : term118 l s) : term340 s l c.
Proof. exact (@lem5312996 l s h1 (term341 l c)). Qed.
Lemma lem5313050 (s : real -> Prop) (l : real) (c : real) : (term340 s l c) = (term342 s l c).
Proof. exact (eq_refl (term340 s l c)). Qed.
Lemma lem5313051 (c : real) (l : real) (s : real -> Prop) (h1 : term118 l s) : term342 s l c.
Proof. exact (EQ_MP (@lem5313050 s l c) (@lem5313049 c l s h1)). Qed.
Lemma lem5313053 (p : Prop) (q : Prop) (r : Prop) : term343 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5313054 (s : real -> Prop) (l : real) (c : real) : term344 s l c.
Proof. exact (@lem5313053 (term345 l c) (term346 s l c) False). Qed.
Lemma lem5313070 (l : real) (c : real) : (term347 l c) = (term348 l c).
Proof. exact (@lem17362 (real_lt l c) (term345 l c)). Qed.
Lemma lem5313072 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5313073 (s : real -> Prop) (l : real) (c : real) : (term350 s l c) = (term351 s l c).
Proof. exact (MK_COMB (@lem5313072 s) (@lem5313070 l c)). Qed.
Lemma lem5313074 (s : real -> Prop) (l : real) (c : real) : (term352 s l c) = (term350 s l c).
Proof. exact (@lem17362 (term22 s) (term353 l c)). Qed.
Lemma lem5313090 (s : real -> Prop) (l : real) (c : real) : (term352 s l c) = (term351 s l c).
Proof. exact (TRANS (@lem5313074 s l c) (@lem5313073 s l c)). Qed.
Lemma lem5313092 (c : real) (l : real) : (real_lt l c) = (term354 c l).
Proof. exact (@lem1988285 c l). Qed.
Lemma lem5313105 (c : real) (l : real) : (real_sub c l) = (term355 c l).
Proof. exact (@lem1982792 c l). Qed.
Lemma lem5313106 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5313107 (c : real) (l : real) : (term356 c l) = (term357 c l).
Proof. exact (MK_COMB (@lem5313106) (@lem5313105 c l)). Qed.
Lemma lem5313108 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5313109 (c : real) (l : real) : (term354 c l) = (term359 c l).
Proof. exact (MK_COMB (@lem5313107 c l) (@lem5313108)). Qed.
Lemma lem5313110 (c : real) (l : real) : (real_lt l c) = (term359 c l).
Proof. exact (TRANS (@lem5313092 c l) (@lem5313109 c l)). Qed.
Lemma lem5313111 (l : real) (c : real) : (term360 l c) = (term361 l c).
Proof. exact (@lem1988295 l (term341 l c)). Qed.
Lemma lem5313113 (x : real) (y : real) : (real_div x y) = (term362 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5313114 (l : real) (c : real) : (term341 l c) = (term363 l c).
Proof. exact (@lem5313113 (real_add l c) term364). Qed.
Lemma lem5313119 (n : nat) : (term365 n) = (term366 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5313121 : term367 = term368.
Proof. exact (@lem5313119 term369). Qed.
Lemma lem5313128 (c : real) (l : real) : (real_add l c) = (real_add c l).
Proof. exact (@lem1982761 c l). Qed.
Lemma lem5313129 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313130 (c : real) (l : real) : (term370 l c) = (term370 c l).
Proof. exact (MK_COMB (@lem5313129) (@lem5313128 c l)). Qed.
Lemma lem5313131 (c : real) (l : real) : (term363 l c) = (term371 c l).
Proof. exact (MK_COMB (@lem5313130 c l) (@lem5313121)). Qed.
Lemma lem5313132 (c : real) (l : real) : (term371 c l) = (term372 c l).
Proof. exact (@lem1982725 term368 (real_add c l)). Qed.
Lemma lem5313139 (c : real) (l : real) : (term372 c l) = (term373 c l).
Proof. exact (@lem1982781 c term368 l). Qed.
Lemma lem5313140 (c : real) (l : real) : (term371 c l) = (term373 c l).
Proof. exact (TRANS (@lem5313132 c l) (@lem5313139 c l)). Qed.
Lemma lem5313141 (c : real) (l : real) : (term363 l c) = (term373 c l).
Proof. exact (TRANS (@lem5313131 c l) (@lem5313140 c l)). Qed.
Lemma lem5313142 (c : real) (l : real) : (term341 l c) = (term373 c l).
Proof. exact (TRANS (@lem5313114 l c) (@lem5313141 c l)). Qed.
Lemma lem5313145 (l : real) : (real_sub l) = (real_sub l).
Proof. exact (eq_refl (real_sub l)). Qed.
Lemma lem5313146 (c : real) (l : real) : (term374 l c) = (term375 c l).
Proof. exact (MK_COMB (@lem5313145 l) (@lem5313142 c l)). Qed.
Lemma lem5313147 (c : real) (l : real) : (term375 c l) = (term376 c l).
Proof. exact (@lem1982792 l (term373 c l)). Qed.
Lemma lem5313148 (c : real) (l : real) : (term377 c l) = (term378 c l).
Proof. exact (@lem1982781 (term379 c) term380 (term379 l)). Qed.
Lemma lem5313149 (l : real) : (term381 l) = (term382 l).
Proof. exact (@lem1982749 term380 term368 l). Qed.
Lemma lem5313150 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem5313152 (x : nat) : (term383 x) = (term384 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5313153 : term380 = term385.
Proof. exact (@lem5313152 term386). Qed.
Lemma lem5313154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313155 : term387 = term388.
Proof. exact (MK_COMB (@lem5313154) (@lem5313153)). Qed.
Lemma lem5313156 : term389 = term390.
Proof. exact (MK_COMB (@lem5313155) (@lem5313150)). Qed.
Lemma lem5313157 : term390 = term391.
Proof. exact (@lem1981613 term380 term392 term392 term364). Qed.
Lemma lem5313159 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313160 : term395 = term396.
Proof. exact (@lem5313159 term386 term369). Qed.
Lemma lem5313161 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313162 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313163 : term399 = term369.
Proof. exact (EQ_MP (@lem5313162) (@lem5313161)). Qed.
Lemma lem5313164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313165 : term396 = term364.
Proof. exact (MK_COMB (@lem5313164) (@lem5313163)). Qed.
Lemma lem5313166 : term395 = term364.
Proof. exact (TRANS (@lem5313160) (@lem5313165)). Qed.
Lemma lem5313168 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5313169 : term402 = term403.
Proof. exact (@lem5313168 term386 term386). Qed.
Lemma lem5313170 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313171 : term405 = term386.
Proof. exact (EQ_MP (@lem5313170) (@lem940073)). Qed.
Lemma lem5313172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313173 : term406 = term392.
Proof. exact (MK_COMB (@lem5313172) (@lem5313171)). Qed.
Lemma lem5313174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5313175 : term403 = term380.
Proof. exact (MK_COMB (@lem5313174) (@lem5313173)). Qed.
Lemma lem5313176 : term402 = term380.
Proof. exact (TRANS (@lem5313169) (@lem5313175)). Qed.
Lemma lem5313177 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5313178 : term407 = term408.
Proof. exact (MK_COMB (@lem5313177) (@lem5313176)). Qed.
Lemma lem5313179 : term391 = term409.
Proof. exact (MK_COMB (@lem5313178) (@lem5313166)). Qed.
Lemma lem5313180 : term390 = term409.
Proof. exact (TRANS (@lem5313157) (@lem5313179)). Qed.
Lemma lem5313183 : term389 = term409.
Proof. exact (TRANS (@lem5313156) (@lem5313180)). Qed.
Lemma lem5313184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313185 : term410 = term411.
Proof. exact (MK_COMB (@lem5313184) (@lem5313183)). Qed.
Lemma lem5313186 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5313187 (l : real) : (term382 l) = (term412 l).
Proof. exact (MK_COMB (@lem5313185) (@lem5313186 l)). Qed.
Lemma lem5313188 (l : real) : (term381 l) = (term412 l).
Proof. exact (TRANS (@lem5313149 l) (@lem5313187 l)). Qed.
Lemma lem5313189 (c : real) : (term381 c) = (term382 c).
Proof. exact (@lem1982749 term380 term368 c). Qed.
Lemma lem5313190 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem5313192 (x : nat) : (term383 x) = (term384 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5313193 : term380 = term385.
Proof. exact (@lem5313192 term386). Qed.
Lemma lem5313194 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313195 : term387 = term388.
Proof. exact (MK_COMB (@lem5313194) (@lem5313193)). Qed.
Lemma lem5313196 : term389 = term390.
Proof. exact (MK_COMB (@lem5313195) (@lem5313190)). Qed.
Lemma lem5313197 : term390 = term391.
Proof. exact (@lem1981613 term380 term392 term392 term364). Qed.
Lemma lem5313199 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313200 : term395 = term396.
Proof. exact (@lem5313199 term386 term369). Qed.
Lemma lem5313201 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313202 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313203 : term399 = term369.
Proof. exact (EQ_MP (@lem5313202) (@lem5313201)). Qed.
Lemma lem5313204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313205 : term396 = term364.
Proof. exact (MK_COMB (@lem5313204) (@lem5313203)). Qed.
Lemma lem5313206 : term395 = term364.
Proof. exact (TRANS (@lem5313200) (@lem5313205)). Qed.
Lemma lem5313208 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5313209 : term402 = term403.
Proof. exact (@lem5313208 term386 term386). Qed.
Lemma lem5313210 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313211 : term405 = term386.
Proof. exact (EQ_MP (@lem5313210) (@lem940073)). Qed.
Lemma lem5313212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313213 : term406 = term392.
Proof. exact (MK_COMB (@lem5313212) (@lem5313211)). Qed.
Lemma lem5313214 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5313215 : term403 = term380.
Proof. exact (MK_COMB (@lem5313214) (@lem5313213)). Qed.
Lemma lem5313216 : term402 = term380.
Proof. exact (TRANS (@lem5313209) (@lem5313215)). Qed.
Lemma lem5313217 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5313218 : term407 = term408.
Proof. exact (MK_COMB (@lem5313217) (@lem5313216)). Qed.
Lemma lem5313219 : term391 = term409.
Proof. exact (MK_COMB (@lem5313218) (@lem5313206)). Qed.
Lemma lem5313220 : term390 = term409.
Proof. exact (TRANS (@lem5313197) (@lem5313219)). Qed.
Lemma lem5313223 : term389 = term409.
Proof. exact (TRANS (@lem5313196) (@lem5313220)). Qed.
Lemma lem5313224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313225 : term410 = term411.
Proof. exact (MK_COMB (@lem5313224) (@lem5313223)). Qed.
Lemma lem5313226 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5313227 (c : real) : (term382 c) = (term412 c).
Proof. exact (MK_COMB (@lem5313225) (@lem5313226 c)). Qed.
Lemma lem5313228 (c : real) : (term381 c) = (term412 c).
Proof. exact (TRANS (@lem5313189 c) (@lem5313227 c)). Qed.
Lemma lem5313229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5313230 (c : real) : (term413 c) = (term414 c).
Proof. exact (MK_COMB (@lem5313229) (@lem5313228 c)). Qed.
Lemma lem5313231 (c : real) (l : real) : (term378 c l) = (term415 c l).
Proof. exact (MK_COMB (@lem5313230 c) (@lem5313188 l)). Qed.
Lemma lem5313232 (c : real) (l : real) : (term377 c l) = (term415 c l).
Proof. exact (TRANS (@lem5313148 c l) (@lem5313231 c l)). Qed.
Lemma lem5313233 (l : real) : (real_add l) = (real_add l).
Proof. exact (eq_refl (real_add l)). Qed.
Lemma lem5313234 (c : real) (l : real) : (term376 c l) = (term416 c l).
Proof. exact (MK_COMB (@lem5313233 l) (@lem5313232 c l)). Qed.
Lemma lem5313235 (c : real) (l : real) : (term416 c l) = (term417 c l).
Proof. exact (@lem1982757 (term412 c) l (term412 l)). Qed.
Lemma lem5313236 (l : real) : (term418 l) = (term419 l).
Proof. exact (@lem1982715 term409 l). Qed.
Lemma lem5313238 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5313239 : term392 = term421.
Proof. exact (@lem5313238 term386). Qed.
Lemma lem5313242 : term422 = term422.
Proof. exact (eq_refl term422). Qed.
Lemma lem5313243 : term423 = term424.
Proof. exact (MK_COMB (@lem5313242) (@lem5313239)). Qed.
Lemma lem5313244 : term425.
Proof. exact (@lem1981473 term380 term364 term392 term392 term392 term364). Qed.
Lemma lem5313246 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313247 : term427 = term428.
Proof. exact (@lem5313246 (NUMERAL 0) term369). Qed.
Lemma lem5313248 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313249 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313250 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313249 h1) (fun h1 : term428 = True => @lem5313248)). Qed.
Lemma lem5313251 : term428 = True.
Proof. exact (EQ_MP (@lem5313250) (@lem5313248)). Qed.
Lemma lem5313252 : term427 = True.
Proof. exact (TRANS (@lem5313247) (@lem5313251)). Qed.
Lemma lem5313253 : True = term427.
Proof. exact (SYM (@lem5313252)). Qed.
Lemma lem5313254 : term427.
Proof. exact (EQ_MP (@lem5313253) (@lem0)). Qed.
Lemma lem5313255 : term430.
Proof. exact (@lem5313244 (@lem5313254)). Qed.
Lemma lem5313257 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313258 : term431 = term432.
Proof. exact (@lem5313257 (NUMERAL 0) term386). Qed.
Lemma lem5313259 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313260 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313261 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313260 h1) (fun h1 : term432 = True => @lem5313259)). Qed.
Lemma lem5313262 : term432 = True.
Proof. exact (EQ_MP (@lem5313261) (@lem5313259)). Qed.
Lemma lem5313263 : term431 = True.
Proof. exact (TRANS (@lem5313258) (@lem5313262)). Qed.
Lemma lem5313264 : True = term431.
Proof. exact (SYM (@lem5313263)). Qed.
Lemma lem5313265 : term431.
Proof. exact (EQ_MP (@lem5313264) (@lem0)). Qed.
Lemma lem5313266 : term434.
Proof. exact (@lem5313255 (@lem5313265)). Qed.
Lemma lem5313268 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313269 : term427 = term428.
Proof. exact (@lem5313268 (NUMERAL 0) term369). Qed.
Lemma lem5313270 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313271 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313272 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313271 h1) (fun h1 : term428 = True => @lem5313270)). Qed.
Lemma lem5313273 : term428 = True.
Proof. exact (EQ_MP (@lem5313272) (@lem5313270)). Qed.
Lemma lem5313274 : term427 = True.
Proof. exact (TRANS (@lem5313269) (@lem5313273)). Qed.
Lemma lem5313275 : True = term427.
Proof. exact (SYM (@lem5313274)). Qed.
Lemma lem5313276 : term427.
Proof. exact (EQ_MP (@lem5313275) (@lem0)). Qed.
Lemma lem5313277 : term435.
Proof. exact (@lem5313266 (@lem5313276)). Qed.
Lemma lem5313279 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313280 : term395 = term396.
Proof. exact (@lem5313279 term386 term369). Qed.
Lemma lem5313281 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313282 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313283 : term399 = term369.
Proof. exact (EQ_MP (@lem5313282) (@lem5313281)). Qed.
Lemma lem5313284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313285 : term396 = term364.
Proof. exact (MK_COMB (@lem5313284) (@lem5313283)). Qed.
Lemma lem5313286 : term395 = term364.
Proof. exact (TRANS (@lem5313280) (@lem5313285)). Qed.
Lemma lem5313288 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5313289 : term402 = term403.
Proof. exact (@lem5313288 term386 term386). Qed.
Lemma lem5313290 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313291 : term405 = term386.
Proof. exact (EQ_MP (@lem5313290) (@lem940073)). Qed.
Lemma lem5313292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313293 : term406 = term392.
Proof. exact (MK_COMB (@lem5313292) (@lem5313291)). Qed.
Lemma lem5313294 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5313295 : term403 = term380.
Proof. exact (MK_COMB (@lem5313294) (@lem5313293)). Qed.
Lemma lem5313296 : term402 = term380.
Proof. exact (TRANS (@lem5313289) (@lem5313295)). Qed.
Lemma lem5313297 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5313298 : term436 = term437.
Proof. exact (MK_COMB (@lem5313297) (@lem5313296)). Qed.
Lemma lem5313299 : term438 = term439.
Proof. exact (MK_COMB (@lem5313298) (@lem5313286)). Qed.
Lemma lem5313302 : term440 = term392.
Proof. exact (@lem1367765 term386 term386). Qed.
Lemma lem5313303 : term441 = term398.
Proof. exact (@lem706885). Qed.
Lemma lem5313304 : (term441 = term398) = (term442 = term369).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term398). Qed.
Lemma lem5313305 : term442 = term369.
Proof. exact (EQ_MP (@lem5313304) (@lem5313303)). Qed.
Lemma lem5313306 : term369 = term442.
Proof. exact (SYM (@lem5313305)). Qed.
Lemma lem5313307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313308 : term364 = term443.
Proof. exact (MK_COMB (@lem5313307) (@lem5313306)). Qed.
Lemma lem5313309 : term437 = term437.
Proof. exact (eq_refl term437). Qed.
Lemma lem5313310 : term439 = term440.
Proof. exact (MK_COMB (@lem5313309) (@lem5313308)). Qed.
Lemma lem5313311 : term439 = term392.
Proof. exact (TRANS (@lem5313310) (@lem5313302)). Qed.
Lemma lem5313312 : term438 = term392.
Proof. exact (TRANS (@lem5313299) (@lem5313311)). Qed.
Lemma lem5313313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313314 : term444 = term445.
Proof. exact (MK_COMB (@lem5313313) (@lem5313312)). Qed.
Lemma lem5313315 : term364 = term364.
Proof. exact (eq_refl term364). Qed.
Lemma lem5313316 : term446 = term395.
Proof. exact (MK_COMB (@lem5313314) (@lem5313315)). Qed.
Lemma lem5313318 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313319 : term395 = term396.
Proof. exact (@lem5313318 term386 term369). Qed.
Lemma lem5313320 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313321 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313322 : term399 = term369.
Proof. exact (EQ_MP (@lem5313321) (@lem5313320)). Qed.
Lemma lem5313323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313324 : term396 = term364.
Proof. exact (MK_COMB (@lem5313323) (@lem5313322)). Qed.
Lemma lem5313325 : term395 = term364.
Proof. exact (TRANS (@lem5313319) (@lem5313324)). Qed.
Lemma lem5313326 : term446 = term364.
Proof. exact (TRANS (@lem5313316) (@lem5313325)). Qed.
Lemma lem5313328 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313329 : term447 = term448.
Proof. exact (@lem5313328 term369 term386). Qed.
Lemma lem5313330 : term449 = term398.
Proof. exact (@lem996237 term398). Qed.
Lemma lem5313331 : (term449 = term398) = (term450 = term369).
Proof. exact (@lem1007663 term398 (BIT1 0) term398). Qed.
Lemma lem5313332 : term450 = term369.
Proof. exact (EQ_MP (@lem5313331) (@lem5313330)). Qed.
Lemma lem5313333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313334 : term448 = term364.
Proof. exact (MK_COMB (@lem5313333) (@lem5313332)). Qed.
Lemma lem5313335 : term447 = term364.
Proof. exact (TRANS (@lem5313329) (@lem5313334)). Qed.
Lemma lem5313336 : term445 = term445.
Proof. exact (eq_refl term445). Qed.
Lemma lem5313337 : term451 = term395.
Proof. exact (MK_COMB (@lem5313336) (@lem5313335)). Qed.
Lemma lem5313339 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313340 : term395 = term396.
Proof. exact (@lem5313339 term386 term369). Qed.
Lemma lem5313341 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313342 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313343 : term399 = term369.
Proof. exact (EQ_MP (@lem5313342) (@lem5313341)). Qed.
Lemma lem5313344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313345 : term396 = term364.
Proof. exact (MK_COMB (@lem5313344) (@lem5313343)). Qed.
Lemma lem5313346 : term395 = term364.
Proof. exact (TRANS (@lem5313340) (@lem5313345)). Qed.
Lemma lem5313347 : term451 = term364.
Proof. exact (TRANS (@lem5313337) (@lem5313346)). Qed.
Lemma lem5313348 : term364 = term451.
Proof. exact (SYM (@lem5313347)). Qed.
Lemma lem5313349 : term446 = term451.
Proof. exact (TRANS (@lem5313326) (@lem5313348)). Qed.
Lemma lem5313350 : term424 = term368.
Proof. exact (@lem5313277 (@lem5313349)). Qed.
Lemma lem5313353 : term423 = term368.
Proof. exact (TRANS (@lem5313243) (@lem5313350)). Qed.
Lemma lem5313354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313355 : term452 = term453.
Proof. exact (MK_COMB (@lem5313354) (@lem5313353)). Qed.
Lemma lem5313356 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5313357 (l : real) : (term419 l) = (term379 l).
Proof. exact (MK_COMB (@lem5313355) (@lem5313356 l)). Qed.
Lemma lem5313358 (l : real) : (term418 l) = (term379 l).
Proof. exact (TRANS (@lem5313236 l) (@lem5313357 l)). Qed.
Lemma lem5313359 (c : real) : (term414 c) = (term414 c).
Proof. exact (eq_refl (term414 c)). Qed.
Lemma lem5313360 (c : real) (l : real) : (term417 c l) = (term454 c l).
Proof. exact (MK_COMB (@lem5313359 c) (@lem5313358 l)). Qed.
Lemma lem5313361 (c : real) (l : real) : (term416 c l) = (term454 c l).
Proof. exact (TRANS (@lem5313235 c l) (@lem5313360 c l)). Qed.
Lemma lem5313362 (c : real) (l : real) : (term376 c l) = (term454 c l).
Proof. exact (TRANS (@lem5313234 c l) (@lem5313361 c l)). Qed.
Lemma lem5313363 (c : real) (l : real) : (term375 c l) = (term454 c l).
Proof. exact (TRANS (@lem5313147 c l) (@lem5313362 c l)). Qed.
Lemma lem5313364 (c : real) (l : real) : (term374 l c) = (term454 c l).
Proof. exact (TRANS (@lem5313146 c l) (@lem5313363 c l)). Qed.
Lemma lem5313365 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5313366 (c : real) (l : real) : (term455 l c) = (term456 c l).
Proof. exact (MK_COMB (@lem5313365) (@lem5313364 c l)). Qed.
Lemma lem5313367 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5313368 (c : real) (l : real) : (term361 l c) = (term457 c l).
Proof. exact (MK_COMB (@lem5313366 c l) (@lem5313367)). Qed.
Lemma lem5313369 (c : real) (l : real) : (term360 l c) = (term457 c l).
Proof. exact (TRANS (@lem5313111 l c) (@lem5313368 c l)). Qed.
Lemma lem5313370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5313371 (c : real) (l : real) : (term164 l c) = (term458 c l).
Proof. exact (MK_COMB (@lem5313370) (@lem5313110 c l)). Qed.
Lemma lem5313372 (c : real) (l : real) : (term348 l c) = (term459 c l).
Proof. exact (MK_COMB (@lem5313371 c l) (@lem5313369 c l)). Qed.
Lemma lem5313374 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5313375 (s : real -> Prop) (c : real) (l : real) : (term351 s l c) = (term460 s c l).
Proof. exact (MK_COMB (@lem5313374 s) (@lem5313372 c l)). Qed.
Lemma lem5313396 (s : real -> Prop) (c : real) (l : real) : (term352 s l c) = (term460 s c l).
Proof. exact (TRANS (@lem5313090 s l c) (@lem5313375 s c l)). Qed.
Lemma lem5313400 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term460 s c l.
Proof. exact (h1). Qed.
Lemma lem5313401 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term459 c l.
Proof. exact (proj2 (@lem5313400 s c l h1)). Qed.
Lemma lem5313403 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term457 c l.
Proof. exact (proj2 (@lem5313401 s c l h1)). Qed.
Lemma lem5313404 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term359 c l.
Proof. exact (proj1 (@lem5313401 s c l h1)). Qed.
Lemma lem5313406 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5313407 : term461 = term431.
Proof. exact (@lem5313406 term358 term392). Qed.
Lemma lem5313409 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5313410 : term392 = term421.
Proof. exact (@lem5313409 term386). Qed.
Lemma lem5313412 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5313413 : term358 = term462.
Proof. exact (@lem5313412 (NUMERAL 0)). Qed.
Lemma lem5313414 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5313415 : term463 = term464.
Proof. exact (MK_COMB (@lem5313414) (@lem5313413)). Qed.
Lemma lem5313416 : term431 = term465.
Proof. exact (MK_COMB (@lem5313415) (@lem5313410)). Qed.
Lemma lem5313417 : term466.
Proof. exact (@lem1980255 term358 term392 term392 term392). Qed.
Lemma lem5313419 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313420 : term431 = term432.
Proof. exact (@lem5313419 (NUMERAL 0) term386). Qed.
Lemma lem5313421 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313422 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313423 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313422 h1) (fun h1 : term432 = True => @lem5313421)). Qed.
Lemma lem5313424 : term432 = True.
Proof. exact (EQ_MP (@lem5313423) (@lem5313421)). Qed.
Lemma lem5313425 : term431 = True.
Proof. exact (TRANS (@lem5313420) (@lem5313424)). Qed.
Lemma lem5313426 : True = term431.
Proof. exact (SYM (@lem5313425)). Qed.
Lemma lem5313427 : term431.
Proof. exact (EQ_MP (@lem5313426) (@lem0)). Qed.
Lemma lem5313428 : term467.
Proof. exact (@lem5313417 (@lem5313427)). Qed.
Lemma lem5313430 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313431 : term431 = term432.
Proof. exact (@lem5313430 (NUMERAL 0) term386). Qed.
Lemma lem5313432 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313433 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313434 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313433 h1) (fun h1 : term432 = True => @lem5313432)). Qed.
Lemma lem5313435 : term432 = True.
Proof. exact (EQ_MP (@lem5313434) (@lem5313432)). Qed.
Lemma lem5313436 : term431 = True.
Proof. exact (TRANS (@lem5313431) (@lem5313435)). Qed.
Lemma lem5313437 : True = term431.
Proof. exact (SYM (@lem5313436)). Qed.
Lemma lem5313438 : term431.
Proof. exact (EQ_MP (@lem5313437) (@lem0)). Qed.
Lemma lem5313439 : term465 = term468.
Proof. exact (@lem5313428 (@lem5313438)). Qed.
Lemma lem5313441 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313442 : term469 = term406.
Proof. exact (@lem5313441 term386 term386). Qed.
Lemma lem5313443 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313444 : term405 = term386.
Proof. exact (EQ_MP (@lem5313443) (@lem940073)). Qed.
Lemma lem5313445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313446 : term406 = term392.
Proof. exact (MK_COMB (@lem5313445) (@lem5313444)). Qed.
Lemma lem5313447 : term469 = term392.
Proof. exact (TRANS (@lem5313442) (@lem5313446)). Qed.
Lemma lem5313449 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313450 : term471 = term358.
Proof. exact (@lem5313449 term386). Qed.
Lemma lem5313451 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5313452 : term472 = term463.
Proof. exact (MK_COMB (@lem5313451) (@lem5313450)). Qed.
Lemma lem5313453 : term468 = term431.
Proof. exact (MK_COMB (@lem5313452) (@lem5313447)). Qed.
Lemma lem5313455 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313456 : term431 = term432.
Proof. exact (@lem5313455 (NUMERAL 0) term386). Qed.
Lemma lem5313457 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313458 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313459 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313458 h1) (fun h1 : term432 = True => @lem5313457)). Qed.
Lemma lem5313460 : term432 = True.
Proof. exact (EQ_MP (@lem5313459) (@lem5313457)). Qed.
Lemma lem5313461 : term431 = True.
Proof. exact (TRANS (@lem5313456) (@lem5313460)). Qed.
Lemma lem5313462 : term468 = True.
Proof. exact (TRANS (@lem5313453) (@lem5313461)). Qed.
Lemma lem5313463 : term465 = True.
Proof. exact (TRANS (@lem5313439) (@lem5313462)). Qed.
Lemma lem5313464 : term431 = True.
Proof. exact (TRANS (@lem5313416) (@lem5313463)). Qed.
Lemma lem5313465 : term461 = True.
Proof. exact (TRANS (@lem5313407) (@lem5313464)). Qed.
Lemma lem5313466 : True = term461.
Proof. exact (SYM (@lem5313465)). Qed.
Lemma lem5313467 : term461.
Proof. exact (EQ_MP (@lem5313466) (@lem0)). Qed.
Lemma lem5313468 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term473 c l.
Proof. exact (conj (@lem5313467) (@lem5313403 s c l h1)). Qed.
Lemma lem5313470 (x : real) (y : real) : term474 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5313471 (c : real) (l : real) : term475 c l.
Proof. exact (@lem5313470 term392 (term454 c l)). Qed.
Lemma lem5313472 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term476 c l.
Proof. exact (@lem5313471 c l (@lem5313468 s c l h1)). Qed.
Lemma lem5313473 (c : real) (l : real) : (term477 c l) = (term454 c l).
Proof. exact (@lem1982733 (term454 c l)). Qed.
Lemma lem5313474 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5313475 (c : real) (l : real) : (term478 c l) = (term456 c l).
Proof. exact (MK_COMB (@lem5313474) (@lem5313473 c l)). Qed.
Lemma lem5313476 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5313477 (c : real) (l : real) : (term476 c l) = (term457 c l).
Proof. exact (MK_COMB (@lem5313475 c l) (@lem5313476)). Qed.
Lemma lem5313478 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term457 c l.
Proof. exact (EQ_MP (@lem5313477 c l) (@lem5313472 s c l h1)). Qed.
Lemma lem5313480 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5313481 : term479 = term480.
Proof. exact (@lem5313480 term358 term368). Qed.
Lemma lem5313482 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem5313484 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5313485 : term358 = term462.
Proof. exact (@lem5313484 (NUMERAL 0)). Qed.
Lemma lem5313486 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5313487 : term463 = term464.
Proof. exact (MK_COMB (@lem5313486) (@lem5313485)). Qed.
Lemma lem5313488 : term480 = term481.
Proof. exact (MK_COMB (@lem5313487) (@lem5313482)). Qed.
Lemma lem5313489 : term482.
Proof. exact (@lem1980255 term358 term364 term392 term392). Qed.
Lemma lem5313491 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313492 : term431 = term432.
Proof. exact (@lem5313491 (NUMERAL 0) term386). Qed.
Lemma lem5313493 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313494 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313495 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313494 h1) (fun h1 : term432 = True => @lem5313493)). Qed.
Lemma lem5313496 : term432 = True.
Proof. exact (EQ_MP (@lem5313495) (@lem5313493)). Qed.
Lemma lem5313497 : term431 = True.
Proof. exact (TRANS (@lem5313492) (@lem5313496)). Qed.
Lemma lem5313498 : True = term431.
Proof. exact (SYM (@lem5313497)). Qed.
Lemma lem5313499 : term431.
Proof. exact (EQ_MP (@lem5313498) (@lem0)). Qed.
Lemma lem5313500 : term483.
Proof. exact (@lem5313489 (@lem5313499)). Qed.
Lemma lem5313502 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313503 : term427 = term428.
Proof. exact (@lem5313502 (NUMERAL 0) term369). Qed.
Lemma lem5313504 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313505 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313506 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313505 h1) (fun h1 : term428 = True => @lem5313504)). Qed.
Lemma lem5313507 : term428 = True.
Proof. exact (EQ_MP (@lem5313506) (@lem5313504)). Qed.
Lemma lem5313508 : term427 = True.
Proof. exact (TRANS (@lem5313503) (@lem5313507)). Qed.
Lemma lem5313509 : True = term427.
Proof. exact (SYM (@lem5313508)). Qed.
Lemma lem5313510 : term427.
Proof. exact (EQ_MP (@lem5313509) (@lem0)). Qed.
Lemma lem5313511 : term481 = term484.
Proof. exact (@lem5313500 (@lem5313510)). Qed.
Lemma lem5313513 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313514 : term469 = term406.
Proof. exact (@lem5313513 term386 term386). Qed.
Lemma lem5313515 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313516 : term405 = term386.
Proof. exact (EQ_MP (@lem5313515) (@lem940073)). Qed.
Lemma lem5313517 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313518 : term406 = term392.
Proof. exact (MK_COMB (@lem5313517) (@lem5313516)). Qed.
Lemma lem5313519 : term469 = term392.
Proof. exact (TRANS (@lem5313514) (@lem5313518)). Qed.
Lemma lem5313521 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313522 : term485 = term358.
Proof. exact (@lem5313521 term369). Qed.
Lemma lem5313523 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5313524 : term486 = term463.
Proof. exact (MK_COMB (@lem5313523) (@lem5313522)). Qed.
Lemma lem5313525 : term484 = term431.
Proof. exact (MK_COMB (@lem5313524) (@lem5313519)). Qed.
Lemma lem5313527 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313528 : term431 = term432.
Proof. exact (@lem5313527 (NUMERAL 0) term386). Qed.
Lemma lem5313529 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313530 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313531 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313530 h1) (fun h1 : term432 = True => @lem5313529)). Qed.
Lemma lem5313532 : term432 = True.
Proof. exact (EQ_MP (@lem5313531) (@lem5313529)). Qed.
Lemma lem5313533 : term431 = True.
Proof. exact (TRANS (@lem5313528) (@lem5313532)). Qed.
Lemma lem5313534 : term484 = True.
Proof. exact (TRANS (@lem5313525) (@lem5313533)). Qed.
Lemma lem5313535 : term481 = True.
Proof. exact (TRANS (@lem5313511) (@lem5313534)). Qed.
Lemma lem5313536 : term480 = True.
Proof. exact (TRANS (@lem5313488) (@lem5313535)). Qed.
Lemma lem5313537 : term479 = True.
Proof. exact (TRANS (@lem5313481) (@lem5313536)). Qed.
Lemma lem5313538 : True = term479.
Proof. exact (SYM (@lem5313537)). Qed.
Lemma lem5313539 : term479.
Proof. exact (EQ_MP (@lem5313538) (@lem0)). Qed.
Lemma lem5313540 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term487 c l.
Proof. exact (conj (@lem5313539) (@lem5313404 s c l h1)). Qed.
Lemma lem5313542 (x : real) (y : real) : term488 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5313543 (c : real) (l : real) : term489 c l.
Proof. exact (@lem5313542 term368 (term355 c l)). Qed.
Lemma lem5313544 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term490 c l.
Proof. exact (@lem5313543 c l (@lem5313540 s c l h1)). Qed.
Lemma lem5313545 (c : real) (l : real) : (term491 c l) = (term492 c l).
Proof. exact (@lem1982781 c term368 (term493 l)). Qed.
Lemma lem5313546 (l : real) : (term494 l) = (term495 l).
Proof. exact (@lem1982749 term368 term380 l). Qed.
Lemma lem5313548 (x : nat) : (term383 x) = (term384 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5313549 : term380 = term385.
Proof. exact (@lem5313548 term386). Qed.
Lemma lem5313552 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5313553 : term496 = term497.
Proof. exact (MK_COMB (@lem5313552) (@lem5313549)). Qed.
Lemma lem5313554 : term497 = term498.
Proof. exact (@lem1981613 term392 term380 term364 term392). Qed.
Lemma lem5313556 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313557 : term447 = term448.
Proof. exact (@lem5313556 term369 term386). Qed.
Lemma lem5313558 : term449 = term398.
Proof. exact (@lem996237 term398). Qed.
Lemma lem5313559 : (term449 = term398) = (term450 = term369).
Proof. exact (@lem1007663 term398 (BIT1 0) term398). Qed.
Lemma lem5313560 : term450 = term369.
Proof. exact (EQ_MP (@lem5313559) (@lem5313558)). Qed.
Lemma lem5313561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313562 : term448 = term364.
Proof. exact (MK_COMB (@lem5313561) (@lem5313560)). Qed.
Lemma lem5313563 : term447 = term364.
Proof. exact (TRANS (@lem5313557) (@lem5313562)). Qed.
Lemma lem5313565 (m : nat) (n : nat) : (term499 m n) = (term401 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5313566 : term500 = term403.
Proof. exact (@lem5313565 term386 term386). Qed.
Lemma lem5313567 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313568 : term405 = term386.
Proof. exact (EQ_MP (@lem5313567) (@lem940073)). Qed.
Lemma lem5313569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313570 : term406 = term392.
Proof. exact (MK_COMB (@lem5313569) (@lem5313568)). Qed.
Lemma lem5313571 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5313572 : term403 = term380.
Proof. exact (MK_COMB (@lem5313571) (@lem5313570)). Qed.
Lemma lem5313573 : term500 = term380.
Proof. exact (TRANS (@lem5313566) (@lem5313572)). Qed.
Lemma lem5313574 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5313575 : term501 = term408.
Proof. exact (MK_COMB (@lem5313574) (@lem5313573)). Qed.
Lemma lem5313576 : term498 = term409.
Proof. exact (MK_COMB (@lem5313575) (@lem5313563)). Qed.
Lemma lem5313577 : term497 = term409.
Proof. exact (TRANS (@lem5313554) (@lem5313576)). Qed.
Lemma lem5313580 : term496 = term409.
Proof. exact (TRANS (@lem5313553) (@lem5313577)). Qed.
Lemma lem5313581 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313582 : term502 = term411.
Proof. exact (MK_COMB (@lem5313581) (@lem5313580)). Qed.
Lemma lem5313583 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5313584 (l : real) : (term495 l) = (term412 l).
Proof. exact (MK_COMB (@lem5313582) (@lem5313583 l)). Qed.
Lemma lem5313585 (l : real) : (term494 l) = (term412 l).
Proof. exact (TRANS (@lem5313546 l) (@lem5313584 l)). Qed.
Lemma lem5313588 (c : real) : (term503 c) = (term503 c).
Proof. exact (eq_refl (term503 c)). Qed.
Lemma lem5313589 (c : real) (l : real) : (term492 c l) = (term504 c l).
Proof. exact (MK_COMB (@lem5313588 c) (@lem5313585 l)). Qed.
Lemma lem5313590 (c : real) (l : real) : (term491 c l) = (term504 c l).
Proof. exact (TRANS (@lem5313545 c l) (@lem5313589 c l)). Qed.
Lemma lem5313591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5313592 (c : real) (l : real) : (term505 c l) = (term506 c l).
Proof. exact (MK_COMB (@lem5313591) (@lem5313590 c l)). Qed.
Lemma lem5313593 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5313594 (c : real) (l : real) : (term490 c l) = (term507 c l).
Proof. exact (MK_COMB (@lem5313592 c l) (@lem5313593)). Qed.
Lemma lem5313595 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term507 c l.
Proof. exact (EQ_MP (@lem5313594 c l) (@lem5313544 s c l h1)). Qed.
Lemma lem5313596 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term508 c l.
Proof. exact (conj (@lem5313595 s c l h1) (@lem5313478 s c l h1)). Qed.
Lemma lem5313598 (x : real) (y : real) : term509 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5313599 (c : real) (l : real) : term510 c l.
Proof. exact (@lem5313598 (term504 c l) (term454 c l)). Qed.
Lemma lem5313600 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term511 c l.
Proof. exact (@lem5313599 c l (@lem5313596 s c l h1)). Qed.
Lemma lem5313601 (c : real) (l : real) : (term512 c l) = (term513 c l).
Proof. exact (@lem1982753 (term379 c) (term412 c) (term412 l) (term379 l)). Qed.
Lemma lem5313602 (c : real) : (term514 c) = (term515 c).
Proof. exact (@lem1982711 term368 term409 c). Qed.
Lemma lem5313608 : term516.
Proof. exact (@lem1981473 term392 term364 term380 term364 term358 term392). Qed.
Lemma lem5313610 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313611 : term427 = term428.
Proof. exact (@lem5313610 (NUMERAL 0) term369). Qed.
Lemma lem5313612 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313613 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313614 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313613 h1) (fun h1 : term428 = True => @lem5313612)). Qed.
Lemma lem5313615 : term428 = True.
Proof. exact (EQ_MP (@lem5313614) (@lem5313612)). Qed.
Lemma lem5313616 : term427 = True.
Proof. exact (TRANS (@lem5313611) (@lem5313615)). Qed.
Lemma lem5313617 : True = term427.
Proof. exact (SYM (@lem5313616)). Qed.
Lemma lem5313618 : term427.
Proof. exact (EQ_MP (@lem5313617) (@lem0)). Qed.
Lemma lem5313619 : term517.
Proof. exact (@lem5313608 (@lem5313618)). Qed.
Lemma lem5313621 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313622 : term427 = term428.
Proof. exact (@lem5313621 (NUMERAL 0) term369). Qed.
Lemma lem5313623 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313624 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313625 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313624 h1) (fun h1 : term428 = True => @lem5313623)). Qed.
Lemma lem5313626 : term428 = True.
Proof. exact (EQ_MP (@lem5313625) (@lem5313623)). Qed.
Lemma lem5313627 : term427 = True.
Proof. exact (TRANS (@lem5313622) (@lem5313626)). Qed.
Lemma lem5313628 : True = term427.
Proof. exact (SYM (@lem5313627)). Qed.
Lemma lem5313629 : term427.
Proof. exact (EQ_MP (@lem5313628) (@lem0)). Qed.
Lemma lem5313630 : term518.
Proof. exact (@lem5313619 (@lem5313629)). Qed.
Lemma lem5313632 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313633 : term431 = term432.
Proof. exact (@lem5313632 (NUMERAL 0) term386). Qed.
Lemma lem5313634 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313635 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313636 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313635 h1) (fun h1 : term432 = True => @lem5313634)). Qed.
Lemma lem5313637 : term432 = True.
Proof. exact (EQ_MP (@lem5313636) (@lem5313634)). Qed.
Lemma lem5313638 : term431 = True.
Proof. exact (TRANS (@lem5313633) (@lem5313637)). Qed.
Lemma lem5313639 : True = term431.
Proof. exact (SYM (@lem5313638)). Qed.
Lemma lem5313640 : term431.
Proof. exact (EQ_MP (@lem5313639) (@lem0)). Qed.
Lemma lem5313641 : term519.
Proof. exact (@lem5313630 (@lem5313640)). Qed.
Lemma lem5313643 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5313644 : term520 = term521.
Proof. exact (@lem5313643 term386 term369). Qed.
Lemma lem5313645 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313646 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313647 : term399 = term369.
Proof. exact (EQ_MP (@lem5313646) (@lem5313645)). Qed.
Lemma lem5313648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313649 : term396 = term364.
Proof. exact (MK_COMB (@lem5313648) (@lem5313647)). Qed.
Lemma lem5313650 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5313651 : term521 = term522.
Proof. exact (MK_COMB (@lem5313650) (@lem5313649)). Qed.
Lemma lem5313652 : term520 = term522.
Proof. exact (TRANS (@lem5313644) (@lem5313651)). Qed.
Lemma lem5313654 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313655 : term395 = term396.
Proof. exact (@lem5313654 term386 term369). Qed.
Lemma lem5313656 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313657 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313658 : term399 = term369.
Proof. exact (EQ_MP (@lem5313657) (@lem5313656)). Qed.
Lemma lem5313659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313660 : term396 = term364.
Proof. exact (MK_COMB (@lem5313659) (@lem5313658)). Qed.
Lemma lem5313661 : term395 = term364.
Proof. exact (TRANS (@lem5313655) (@lem5313660)). Qed.
Lemma lem5313662 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5313663 : term523 = term524.
Proof. exact (MK_COMB (@lem5313662) (@lem5313661)). Qed.
Lemma lem5313664 : term525 = term526.
Proof. exact (MK_COMB (@lem5313663) (@lem5313652)). Qed.
Lemma lem5313666 (m : nat) : (term527 m) = term358.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5313667 : term526 = term358.
Proof. exact (@lem5313666 term369). Qed.
Lemma lem5313668 : term525 = term358.
Proof. exact (TRANS (@lem5313664) (@lem5313667)). Qed.
Lemma lem5313669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313670 : term528 = term529.
Proof. exact (MK_COMB (@lem5313669) (@lem5313668)). Qed.
Lemma lem5313671 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem5313672 : term530 = term471.
Proof. exact (MK_COMB (@lem5313670) (@lem5313671)). Qed.
Lemma lem5313674 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313675 : term471 = term358.
Proof. exact (@lem5313674 term386). Qed.
Lemma lem5313676 : term530 = term358.
Proof. exact (TRANS (@lem5313672) (@lem5313675)). Qed.
Lemma lem5313678 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313679 : term531 = term532.
Proof. exact (@lem5313678 term369 term369). Qed.
Lemma lem5313680 : (term404 = (BIT1 0)) = (term533 = term534).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313681 : term533 = term534.
Proof. exact (EQ_MP (@lem5313680) (@lem940073)). Qed.
Lemma lem5313682 : (term533 = term534) = (term535 = term536).
Proof. exact (@lem1008952 term398 term534). Qed.
Lemma lem5313683 : term535 = term536.
Proof. exact (EQ_MP (@lem5313682) (@lem5313681)). Qed.
Lemma lem5313684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313685 : term532 = term537.
Proof. exact (MK_COMB (@lem5313684) (@lem5313683)). Qed.
Lemma lem5313686 : term531 = term537.
Proof. exact (TRANS (@lem5313679) (@lem5313685)). Qed.
Lemma lem5313687 : term529 = term529.
Proof. exact (eq_refl term529). Qed.
Lemma lem5313688 : term538 = term539.
Proof. exact (MK_COMB (@lem5313687) (@lem5313686)). Qed.
Lemma lem5313690 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313691 : term539 = term358.
Proof. exact (@lem5313690 term536). Qed.
Lemma lem5313692 : term538 = term358.
Proof. exact (TRANS (@lem5313688) (@lem5313691)). Qed.
Lemma lem5313693 : term358 = term538.
Proof. exact (SYM (@lem5313692)). Qed.
Lemma lem5313694 : term530 = term538.
Proof. exact (TRANS (@lem5313676) (@lem5313693)). Qed.
Lemma lem5313696 : term540 = term462.
Proof. exact (@lem5313641 (@lem5313694)). Qed.
Lemma lem5313698 (x : real) : (term541 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5313699 : term462 = term358.
Proof. exact (@lem5313698 term358). Qed.
Lemma lem5313700 : term540 = term358.
Proof. exact (TRANS (@lem5313696) (@lem5313699)). Qed.
Lemma lem5313701 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313702 : term542 = term529.
Proof. exact (MK_COMB (@lem5313701) (@lem5313700)). Qed.
Lemma lem5313703 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5313704 (c : real) : (term515 c) = (term543 c).
Proof. exact (MK_COMB (@lem5313702) (@lem5313703 c)). Qed.
Lemma lem5313705 (c : real) : (term514 c) = (term543 c).
Proof. exact (TRANS (@lem5313602 c) (@lem5313704 c)). Qed.
Lemma lem5313706 (c : real) : (term543 c) = term358.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5313707 (c : real) : (term514 c) = term358.
Proof. exact (TRANS (@lem5313705 c) (@lem5313706 c)). Qed.
Lemma lem5313708 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5313709 (c : real) : (term544 c) = term545.
Proof. exact (MK_COMB (@lem5313708) (@lem5313707 c)). Qed.
Lemma lem5313710 (l : real) : (term546 l) = (term547 l).
Proof. exact (@lem1982711 term409 term368 l). Qed.
Lemma lem5313716 : term548.
Proof. exact (@lem1981473 term380 term364 term392 term364 term358 term392). Qed.
Lemma lem5313718 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313719 : term427 = term428.
Proof. exact (@lem5313718 (NUMERAL 0) term369). Qed.
Lemma lem5313720 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313721 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313722 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313721 h1) (fun h1 : term428 = True => @lem5313720)). Qed.
Lemma lem5313723 : term428 = True.
Proof. exact (EQ_MP (@lem5313722) (@lem5313720)). Qed.
Lemma lem5313724 : term427 = True.
Proof. exact (TRANS (@lem5313719) (@lem5313723)). Qed.
Lemma lem5313725 : True = term427.
Proof. exact (SYM (@lem5313724)). Qed.
Lemma lem5313726 : term427.
Proof. exact (EQ_MP (@lem5313725) (@lem0)). Qed.
Lemma lem5313727 : term549.
Proof. exact (@lem5313716 (@lem5313726)). Qed.
Lemma lem5313729 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313730 : term427 = term428.
Proof. exact (@lem5313729 (NUMERAL 0) term369). Qed.
Lemma lem5313731 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5313732 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5313733 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5313732 h1) (fun h1 : term428 = True => @lem5313731)). Qed.
Lemma lem5313734 : term428 = True.
Proof. exact (EQ_MP (@lem5313733) (@lem5313731)). Qed.
Lemma lem5313735 : term427 = True.
Proof. exact (TRANS (@lem5313730) (@lem5313734)). Qed.
Lemma lem5313736 : True = term427.
Proof. exact (SYM (@lem5313735)). Qed.
Lemma lem5313737 : term427.
Proof. exact (EQ_MP (@lem5313736) (@lem0)). Qed.
Lemma lem5313738 : term550.
Proof. exact (@lem5313727 (@lem5313737)). Qed.
Lemma lem5313740 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313741 : term431 = term432.
Proof. exact (@lem5313740 (NUMERAL 0) term386). Qed.
Lemma lem5313742 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313743 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313744 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313743 h1) (fun h1 : term432 = True => @lem5313742)). Qed.
Lemma lem5313745 : term432 = True.
Proof. exact (EQ_MP (@lem5313744) (@lem5313742)). Qed.
Lemma lem5313746 : term431 = True.
Proof. exact (TRANS (@lem5313741) (@lem5313745)). Qed.
Lemma lem5313747 : True = term431.
Proof. exact (SYM (@lem5313746)). Qed.
Lemma lem5313748 : term431.
Proof. exact (EQ_MP (@lem5313747) (@lem0)). Qed.
Lemma lem5313749 : term551.
Proof. exact (@lem5313738 (@lem5313748)). Qed.
Lemma lem5313751 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313752 : term395 = term396.
Proof. exact (@lem5313751 term386 term369). Qed.
Lemma lem5313753 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313754 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313755 : term399 = term369.
Proof. exact (EQ_MP (@lem5313754) (@lem5313753)). Qed.
Lemma lem5313756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313757 : term396 = term364.
Proof. exact (MK_COMB (@lem5313756) (@lem5313755)). Qed.
Lemma lem5313758 : term395 = term364.
Proof. exact (TRANS (@lem5313752) (@lem5313757)). Qed.
Lemma lem5313760 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5313761 : term520 = term521.
Proof. exact (@lem5313760 term386 term369). Qed.
Lemma lem5313762 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5313763 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5313764 : term399 = term369.
Proof. exact (EQ_MP (@lem5313763) (@lem5313762)). Qed.
Lemma lem5313765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313766 : term396 = term364.
Proof. exact (MK_COMB (@lem5313765) (@lem5313764)). Qed.
Lemma lem5313767 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5313768 : term521 = term522.
Proof. exact (MK_COMB (@lem5313767) (@lem5313766)). Qed.
Lemma lem5313769 : term520 = term522.
Proof. exact (TRANS (@lem5313761) (@lem5313768)). Qed.
Lemma lem5313770 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5313771 : term552 = term553.
Proof. exact (MK_COMB (@lem5313770) (@lem5313769)). Qed.
Lemma lem5313772 : term554 = term555.
Proof. exact (MK_COMB (@lem5313771) (@lem5313758)). Qed.
Lemma lem5313774 (m : nat) : (term556 m) = term358.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5313775 : term555 = term358.
Proof. exact (@lem5313774 term369). Qed.
Lemma lem5313776 : term554 = term358.
Proof. exact (TRANS (@lem5313772) (@lem5313775)). Qed.
Lemma lem5313777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313778 : term557 = term529.
Proof. exact (MK_COMB (@lem5313777) (@lem5313776)). Qed.
Lemma lem5313779 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem5313780 : term558 = term471.
Proof. exact (MK_COMB (@lem5313778) (@lem5313779)). Qed.
Lemma lem5313782 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313783 : term471 = term358.
Proof. exact (@lem5313782 term386). Qed.
Lemma lem5313784 : term558 = term358.
Proof. exact (TRANS (@lem5313780) (@lem5313783)). Qed.
Lemma lem5313786 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5313787 : term531 = term532.
Proof. exact (@lem5313786 term369 term369). Qed.
Lemma lem5313788 : (term404 = (BIT1 0)) = (term533 = term534).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5313789 : term533 = term534.
Proof. exact (EQ_MP (@lem5313788) (@lem940073)). Qed.
Lemma lem5313790 : (term533 = term534) = (term535 = term536).
Proof. exact (@lem1008952 term398 term534). Qed.
Lemma lem5313791 : term535 = term536.
Proof. exact (EQ_MP (@lem5313790) (@lem5313789)). Qed.
Lemma lem5313792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5313793 : term532 = term537.
Proof. exact (MK_COMB (@lem5313792) (@lem5313791)). Qed.
Lemma lem5313794 : term531 = term537.
Proof. exact (TRANS (@lem5313787) (@lem5313793)). Qed.
Lemma lem5313795 : term529 = term529.
Proof. exact (eq_refl term529). Qed.
Lemma lem5313796 : term538 = term539.
Proof. exact (MK_COMB (@lem5313795) (@lem5313794)). Qed.
Lemma lem5313798 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313799 : term539 = term358.
Proof. exact (@lem5313798 term536). Qed.
Lemma lem5313800 : term538 = term358.
Proof. exact (TRANS (@lem5313796) (@lem5313799)). Qed.
Lemma lem5313801 : term358 = term538.
Proof. exact (SYM (@lem5313800)). Qed.
Lemma lem5313802 : term558 = term538.
Proof. exact (TRANS (@lem5313784) (@lem5313801)). Qed.
Lemma lem5313804 : term559 = term462.
Proof. exact (@lem5313749 (@lem5313802)). Qed.
Lemma lem5313806 (x : real) : (term541 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5313807 : term462 = term358.
Proof. exact (@lem5313806 term358). Qed.
Lemma lem5313808 : term559 = term358.
Proof. exact (TRANS (@lem5313804) (@lem5313807)). Qed.
Lemma lem5313809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5313810 : term560 = term529.
Proof. exact (MK_COMB (@lem5313809) (@lem5313808)). Qed.
Lemma lem5313811 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5313812 (l : real) : (term547 l) = (term543 l).
Proof. exact (MK_COMB (@lem5313810) (@lem5313811 l)). Qed.
Lemma lem5313813 (l : real) : (term546 l) = (term543 l).
Proof. exact (TRANS (@lem5313710 l) (@lem5313812 l)). Qed.
Lemma lem5313814 (l : real) : (term543 l) = term358.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5313815 (l : real) : (term546 l) = term358.
Proof. exact (TRANS (@lem5313813 l) (@lem5313814 l)). Qed.
Lemma lem5313816 (c : real) (l : real) : (term513 c l) = term561.
Proof. exact (MK_COMB (@lem5313709 c) (@lem5313815 l)). Qed.
Lemma lem5313817 (c : real) (l : real) : (term512 c l) = term561.
Proof. exact (TRANS (@lem5313601 c l) (@lem5313816 c l)). Qed.
Lemma lem5313818 : term561 = term358.
Proof. exact (@lem1982721 term358). Qed.
Lemma lem5313819 (c : real) (l : real) : (term512 c l) = term358.
Proof. exact (TRANS (@lem5313817 c l) (@lem5313818)). Qed.
Lemma lem5313820 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5313821 (c : real) (l : real) : (term562 c l) = term563.
Proof. exact (MK_COMB (@lem5313820) (@lem5313819 c l)). Qed.
Lemma lem5313822 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5313823 (c : real) (l : real) : (term511 c l) = term564.
Proof. exact (MK_COMB (@lem5313821 c l) (@lem5313822)). Qed.
Lemma lem5313824 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term564.
Proof. exact (EQ_MP (@lem5313823 c l) (@lem5313600 s c l h1)). Qed.
Lemma lem5313826 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5313827 : term564 = term565.
Proof. exact (@lem5313826 term358 term358). Qed.
Lemma lem5313829 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5313830 : term358 = term462.
Proof. exact (@lem5313829 (NUMERAL 0)). Qed.
Lemma lem5313832 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5313833 : term358 = term462.
Proof. exact (@lem5313832 (NUMERAL 0)). Qed.
Lemma lem5313834 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5313835 : term463 = term464.
Proof. exact (MK_COMB (@lem5313834) (@lem5313833)). Qed.
Lemma lem5313836 : term565 = term566.
Proof. exact (MK_COMB (@lem5313835) (@lem5313830)). Qed.
Lemma lem5313837 : term567.
Proof. exact (@lem1980255 term358 term392 term358 term392). Qed.
Lemma lem5313839 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313840 : term431 = term432.
Proof. exact (@lem5313839 (NUMERAL 0) term386). Qed.
Lemma lem5313841 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313842 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313843 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313842 h1) (fun h1 : term432 = True => @lem5313841)). Qed.
Lemma lem5313844 : term432 = True.
Proof. exact (EQ_MP (@lem5313843) (@lem5313841)). Qed.
Lemma lem5313845 : term431 = True.
Proof. exact (TRANS (@lem5313840) (@lem5313844)). Qed.
Lemma lem5313846 : True = term431.
Proof. exact (SYM (@lem5313845)). Qed.
Lemma lem5313847 : term431.
Proof. exact (EQ_MP (@lem5313846) (@lem0)). Qed.
Lemma lem5313848 : term568.
Proof. exact (@lem5313837 (@lem5313847)). Qed.
Lemma lem5313850 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313851 : term431 = term432.
Proof. exact (@lem5313850 (NUMERAL 0) term386). Qed.
Lemma lem5313852 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5313853 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5313854 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5313853 h1) (fun h1 : term432 = True => @lem5313852)). Qed.
Lemma lem5313855 : term432 = True.
Proof. exact (EQ_MP (@lem5313854) (@lem5313852)). Qed.
Lemma lem5313856 : term431 = True.
Proof. exact (TRANS (@lem5313851) (@lem5313855)). Qed.
Lemma lem5313857 : True = term431.
Proof. exact (SYM (@lem5313856)). Qed.
Lemma lem5313858 : term431.
Proof. exact (EQ_MP (@lem5313857) (@lem0)). Qed.
Lemma lem5313859 : term566 = term569.
Proof. exact (@lem5313848 (@lem5313858)). Qed.
Lemma lem5313861 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313862 : term471 = term358.
Proof. exact (@lem5313861 term386). Qed.
Lemma lem5313864 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5313865 : term471 = term358.
Proof. exact (@lem5313864 term386). Qed.
Lemma lem5313866 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5313867 : term472 = term463.
Proof. exact (MK_COMB (@lem5313866) (@lem5313865)). Qed.
Lemma lem5313868 : term569 = term565.
Proof. exact (MK_COMB (@lem5313867) (@lem5313862)). Qed.
Lemma lem5313870 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5313871 : term565 = term570.
Proof. exact (@lem5313870 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5313872 : term570 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5313873 : term565 = False.
Proof. exact (TRANS (@lem5313871) (@lem5313872)). Qed.
Lemma lem5313874 : term569 = False.
Proof. exact (TRANS (@lem5313868) (@lem5313873)). Qed.
Lemma lem5313875 : term566 = False.
Proof. exact (TRANS (@lem5313859) (@lem5313874)). Qed.
Lemma lem5313876 : term565 = False.
Proof. exact (TRANS (@lem5313836) (@lem5313875)). Qed.
Lemma lem5313877 : term564 = False.
Proof. exact (TRANS (@lem5313827) (@lem5313876)). Qed.
Lemma lem5313878 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : False.
Proof. exact (EQ_MP (@lem5313877) (@lem5313824 s c l h1)). Qed.
Lemma lem5313880 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : term460 s c l.
Proof. exact (h1). Qed.
Lemma lem5313881 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : (term460 s c l) = False.
Proof. exact (prop_ext (fun h2 : term460 s c l => @lem5313878 s c l h1) (fun h2 : False => @lem5313880 s c l h1)). Qed.
Lemma lem5313882 (s : real -> Prop) (c : real) (l : real) (h1 : term460 s c l) : False.
Proof. exact (EQ_MP (@lem5313881 s c l h1) (@lem5313880 s c l h1)). Qed.
Lemma lem5313883 (s : real -> Prop) (l : real) (c : real) (h1 : term352 s l c) : term352 s l c.
Proof. exact (h1). Qed.
Lemma lem5313884 (s : real -> Prop) (l : real) (c : real) (h1 : term352 s l c) : term460 s c l.
Proof. exact (EQ_MP (@lem5313396 s c l) (@lem5313883 s l c h1)). Qed.
Lemma lem5313885 (s : real -> Prop) (l : real) (c : real) (h1 : term352 s l c) : (term460 s c l) = False.
Proof. exact (prop_ext (fun h2 : term460 s c l => @lem5313882 s c l h2) (fun h2 : False => @lem5313884 s l c h1)). Qed.
Lemma lem5313886 (s : real -> Prop) (l : real) (c : real) (h1 : term352 s l c) : False.
Proof. exact (EQ_MP (@lem5313885 s l c h1) (@lem5313884 s l c h1)). Qed.
Lemma lem5313887 (s : real -> Prop) (l : real) (c : real) : term571 s l c.
Proof. exact (fun h0 : term352 s l c => @lem5313886 s l c h0). Qed.
Lemma lem5313888 (s : real -> Prop) (l : real) (c : real) : term572 s l c.
Proof. exact (@lem1386578 (term573 s l c)). Qed.
Lemma lem5313891 (s : real -> Prop) (l : real) (c : real) : term573 s l c.
Proof. exact (@lem5313888 s l c (@lem5313887 s l c)). Qed.
Lemma lem5313892 (l : real) (c : real) (s : real -> Prop) (h1 : term22 s) : term353 l c.
Proof. exact (@lem5313891 s l c (@lem5312995 s h1)). Qed.
Lemma lem5313893 (s : real -> Prop) (l : real) (c : real) (h1 : term22 s) (h2 : real_lt l c) : term345 l c.
Proof. exact (@lem5313892 l c s h1 (@lem5313048 l c h2)). Qed.
Lemma lem5313894 (s : real -> Prop) (l : real) (c : real) (h1 : term346 s l c) : term346 s l c.
Proof. exact (h1). Qed.
Lemma lem5313895 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term574 s x0 l c) : term574 s x0 l c.
Proof. exact (h1). Qed.
Lemma lem5313896 (x0 : real) (l : real) (c : real) (h1 : term575 x0 l c) : term575 x0 l c.
Proof. exact (h1). Qed.
Lemma lem5313897 (x0 : real) (s : real -> Prop) (h1 : @IN real x0 s) : @IN real x0 s.
Proof. exact (h1). Qed.
Lemma lem5313898 (x : real) (s : real -> Prop) (c : real) (h1 : term25 s c) : term61 s c x.
Proof. exact (@lem5313043 s c h1 x). Qed.
Lemma lem5313899 (s : real -> Prop) (c : real) (x : real) : (term61 s c x) = (term54 s c x).
Proof. exact (eq_refl (term61 s c x)). Qed.
Lemma lem5313902 (x : real) (s : real -> Prop) (c : real) (h1 : term25 s c) : term54 s c x.
Proof. exact (EQ_MP (@lem5313899 s c x) (@lem5313898 x s c h1)). Qed.
Lemma lem5313903 (x0 : real) (s : real -> Prop) (c : real) (h1 : term25 s c) : term54 s c x0.
Proof. exact (@lem5313902 x0 s c h1). Qed.
Lemma lem5313904 (c : real) (x0 : real) (s : real -> Prop) (h1 : term25 s c) (h2 : @IN real x0 s) : real_le c x0.
Proof. exact (@lem5313903 x0 s c h1 (@lem5313897 x0 s h2)). Qed.
Lemma lem5313916 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5313917 (x0 : real) (l : real) (c : real) : (term576 x0 l c) = (term577 x0 l c).
Proof. exact (@lem5313916 (term575 x0 l c)). Qed.
Lemma lem5313918 (c : real) (x0 : real) : (term578 c x0) = (term578 c x0).
Proof. exact (eq_refl (term578 c x0)). Qed.
Lemma lem5313919 (x0 : real) (l : real) (c : real) : (term579 x0 l c) = (term580 x0 l c).
Proof. exact (MK_COMB (@lem5313918 c x0) (@lem5313917 x0 l c)). Qed.
Lemma lem5313922 (x0 : real) (s : real -> Prop) : (term581 x0 s) = (term581 x0 s).
Proof. exact (eq_refl (term581 x0 s)). Qed.
Lemma lem5313923 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term582 s x0 l c) = (term583 s x0 l c).
Proof. exact (MK_COMB (@lem5313922 x0 s) (@lem5313919 x0 l c)). Qed.
Lemma lem5313926 (l : real) (c : real) : (term150 l c) = (term150 l c).
Proof. exact (eq_refl (term150 l c)). Qed.
Lemma lem5313927 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term584 s x0 l c) = (term585 s x0 l c).
Proof. exact (MK_COMB (@lem5313926 l c) (@lem5313923 s x0 l c)). Qed.
Lemma lem5313930 (s : real -> Prop) : (term586 s) = (term586 s).
Proof. exact (eq_refl (term586 s)). Qed.
Lemma lem5313931 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term587 s x0 l c) = (term588 s x0 l c).
Proof. exact (MK_COMB (@lem5313930 s) (@lem5313927 s x0 l c)). Qed.
Lemma lem5313934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5313936 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term589 s x0 l c) = (term590 s x0 l c).
Proof. exact (MK_COMB (@lem5313934) (@lem5313931 s x0 l c)). Qed.
Lemma lem5313943 (x0 : real) (l : real) (c : real) : (term591 x0 l c) = (term575 x0 l c).
Proof. exact (@lem16933 (term575 x0 l c)). Qed.
Lemma lem5313945 (c : real) (x0 : real) : (term592 c x0) = (term592 c x0).
Proof. exact (eq_refl (term592 c x0)). Qed.
Lemma lem5313946 (x0 : real) (l : real) (c : real) : (term593 x0 l c) = (term594 x0 l c).
Proof. exact (MK_COMB (@lem5313945 c x0) (@lem5313943 x0 l c)). Qed.
Lemma lem5313947 (x0 : real) (l : real) (c : real) : (term595 x0 l c) = (term593 x0 l c).
Proof. exact (@lem17362 (real_le c x0) (term577 x0 l c)). Qed.
Lemma lem5313948 (x0 : real) (l : real) (c : real) : (term595 x0 l c) = (term594 x0 l c).
Proof. exact (TRANS (@lem5313947 x0 l c) (@lem5313946 x0 l c)). Qed.
Lemma lem5313950 (x0 : real) (s : real -> Prop) : (term596 x0 s) = (term596 x0 s).
Proof. exact (eq_refl (term596 x0 s)). Qed.
Lemma lem5313951 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term597 s x0 l c) = (term598 s x0 l c).
Proof. exact (MK_COMB (@lem5313950 x0 s) (@lem5313948 x0 l c)). Qed.
Lemma lem5313952 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term599 s x0 l c) = (term597 s x0 l c).
Proof. exact (@lem17362 (@IN real x0 s) (term580 x0 l c)). Qed.
Lemma lem5313953 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term599 s x0 l c) = (term598 s x0 l c).
Proof. exact (TRANS (@lem5313952 s x0 l c) (@lem5313951 s x0 l c)). Qed.
Lemma lem5313955 (l : real) (c : real) : (term164 l c) = (term164 l c).
Proof. exact (eq_refl (term164 l c)). Qed.
Lemma lem5313956 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term600 s x0 l c) = (term601 s x0 l c).
Proof. exact (MK_COMB (@lem5313955 l c) (@lem5313953 s x0 l c)). Qed.
Lemma lem5313957 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term602 s x0 l c) = (term600 s x0 l c).
Proof. exact (@lem17362 (real_lt l c) (term583 s x0 l c)). Qed.
Lemma lem5313958 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term602 s x0 l c) = (term601 s x0 l c).
Proof. exact (TRANS (@lem5313957 s x0 l c) (@lem5313956 s x0 l c)). Qed.
Lemma lem5313960 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5313961 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term603 s x0 l c) = (term604 s x0 l c).
Proof. exact (MK_COMB (@lem5313960 s) (@lem5313958 s x0 l c)). Qed.
Lemma lem5313962 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term590 s x0 l c) = (term603 s x0 l c).
Proof. exact (@lem17362 (term22 s) (term585 s x0 l c)). Qed.
Lemma lem5313963 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term590 s x0 l c) = (term604 s x0 l c).
Proof. exact (TRANS (@lem5313962 s x0 l c) (@lem5313961 s x0 l c)). Qed.
Lemma lem5313984 (s : real -> Prop) (x0 : real) (l : real) (c : real) : (term589 s x0 l c) = (term604 s x0 l c).
Proof. exact (TRANS (@lem5313936 s x0 l c) (@lem5313963 s x0 l c)). Qed.
Lemma lem5313986 (c : real) (l : real) : (real_lt l c) = (term354 c l).
Proof. exact (@lem1988285 c l). Qed.
Lemma lem5313999 (c : real) (l : real) : (real_sub c l) = (term355 c l).
Proof. exact (@lem1982792 c l). Qed.
Lemma lem5314000 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314001 (c : real) (l : real) : (term356 c l) = (term357 c l).
Proof. exact (MK_COMB (@lem5314000) (@lem5313999 c l)). Qed.
Lemma lem5314002 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314003 (c : real) (l : real) : (term354 c l) = (term359 c l).
Proof. exact (MK_COMB (@lem5314001 c l) (@lem5314002)). Qed.
Lemma lem5314004 (c : real) (l : real) : (real_lt l c) = (term359 c l).
Proof. exact (TRANS (@lem5313986 c l) (@lem5314003 c l)). Qed.
Lemma lem5314006 (x0 : real) (c : real) : (real_le c x0) = (term605 x0 c).
Proof. exact (@lem1988287 x0 c). Qed.
Lemma lem5314012 (x0 : real) (c : real) : (real_sub x0 c) = (term355 x0 c).
Proof. exact (@lem1982792 x0 c). Qed.
Lemma lem5314017 (c : real) (x0 : real) : (term355 x0 c) = (term606 c x0).
Proof. exact (@lem1982761 (term493 c) x0). Qed.
Lemma lem5314019 (c : real) (x0 : real) : (real_sub x0 c) = (term606 c x0).
Proof. exact (TRANS (@lem5314012 x0 c) (@lem5314017 c x0)). Qed.
Lemma lem5314020 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5314021 (c : real) (x0 : real) : (term607 x0 c) = (term608 c x0).
Proof. exact (MK_COMB (@lem5314020) (@lem5314019 c x0)). Qed.
Lemma lem5314022 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314023 (c : real) (x0 : real) : (term605 x0 c) = (term609 c x0).
Proof. exact (MK_COMB (@lem5314021 c x0) (@lem5314022)). Qed.
Lemma lem5314024 (c : real) (x0 : real) : (real_le c x0) = (term609 c x0).
Proof. exact (TRANS (@lem5314006 x0 c) (@lem5314023 c x0)). Qed.
Lemma lem5314025 (l : real) (c : real) (x0 : real) : (term575 x0 l c) = (term610 l c x0).
Proof. exact (@lem1988285 (term341 l c) x0). Qed.
Lemma lem5314026 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem5314028 (x : real) (y : real) : (real_div x y) = (term362 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5314029 (l : real) (c : real) : (term341 l c) = (term363 l c).
Proof. exact (@lem5314028 (real_add l c) term364). Qed.
Lemma lem5314034 (n : nat) : (term365 n) = (term366 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5314036 : term367 = term368.
Proof. exact (@lem5314034 term369). Qed.
Lemma lem5314043 (c : real) (l : real) : (real_add l c) = (real_add c l).
Proof. exact (@lem1982761 c l). Qed.
Lemma lem5314044 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314045 (c : real) (l : real) : (term370 l c) = (term370 c l).
Proof. exact (MK_COMB (@lem5314044) (@lem5314043 c l)). Qed.
Lemma lem5314046 (c : real) (l : real) : (term363 l c) = (term371 c l).
Proof. exact (MK_COMB (@lem5314045 c l) (@lem5314036)). Qed.
Lemma lem5314047 (c : real) (l : real) : (term371 c l) = (term372 c l).
Proof. exact (@lem1982725 term368 (real_add c l)). Qed.
Lemma lem5314054 (c : real) (l : real) : (term372 c l) = (term373 c l).
Proof. exact (@lem1982781 c term368 l). Qed.
Lemma lem5314055 (c : real) (l : real) : (term371 c l) = (term373 c l).
Proof. exact (TRANS (@lem5314047 c l) (@lem5314054 c l)). Qed.
Lemma lem5314056 (c : real) (l : real) : (term363 l c) = (term373 c l).
Proof. exact (TRANS (@lem5314046 c l) (@lem5314055 c l)). Qed.
Lemma lem5314057 (c : real) (l : real) : (term341 l c) = (term373 c l).
Proof. exact (TRANS (@lem5314029 l c) (@lem5314056 c l)). Qed.
Lemma lem5314058 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5314059 (c : real) (l : real) : (term611 l c) = (term612 c l).
Proof. exact (MK_COMB (@lem5314058) (@lem5314057 c l)). Qed.
Lemma lem5314060 (c : real) (l : real) (x0 : real) : (term613 l c x0) = (term614 c l x0).
Proof. exact (MK_COMB (@lem5314059 c l) (@lem5314026 x0)). Qed.
Lemma lem5314061 (c : real) (l : real) (x0 : real) : (term614 c l x0) = (term615 c l x0).
Proof. exact (@lem1982792 (term373 c l) x0). Qed.
Lemma lem5314070 (c : real) (l : real) (x0 : real) : (term615 c l x0) = (term616 c l x0).
Proof. exact (@lem1982755 (term379 c) (term379 l) (term493 x0)). Qed.
Lemma lem5314071 (c : real) (l : real) (x0 : real) : (term614 c l x0) = (term616 c l x0).
Proof. exact (TRANS (@lem5314061 c l x0) (@lem5314070 c l x0)). Qed.
Lemma lem5314072 (c : real) (l : real) (x0 : real) : (term613 l c x0) = (term616 c l x0).
Proof. exact (TRANS (@lem5314060 c l x0) (@lem5314071 c l x0)). Qed.
Lemma lem5314073 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314074 (c : real) (l : real) (x0 : real) : (term617 l c x0) = (term618 c l x0).
Proof. exact (MK_COMB (@lem5314073) (@lem5314072 c l x0)). Qed.
Lemma lem5314075 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314076 (c : real) (l : real) (x0 : real) : (term610 l c x0) = (term619 c l x0).
Proof. exact (MK_COMB (@lem5314074 c l x0) (@lem5314075)). Qed.
Lemma lem5314077 (c : real) (l : real) (x0 : real) : (term575 x0 l c) = (term619 c l x0).
Proof. exact (TRANS (@lem5314025 l c x0) (@lem5314076 c l x0)). Qed.
Lemma lem5314078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5314079 (c : real) (x0 : real) : (term592 c x0) = (term620 c x0).
Proof. exact (MK_COMB (@lem5314078) (@lem5314024 c x0)). Qed.
Lemma lem5314080 (c : real) (l : real) (x0 : real) : (term594 x0 l c) = (term621 c l x0).
Proof. exact (MK_COMB (@lem5314079 c x0) (@lem5314077 c l x0)). Qed.
Lemma lem5314082 (x0 : real) (s : real -> Prop) : (term596 x0 s) = (term596 x0 s).
Proof. exact (eq_refl (term596 x0 s)). Qed.
Lemma lem5314083 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term598 s x0 l c) = (term622 s c l x0).
Proof. exact (MK_COMB (@lem5314082 x0 s) (@lem5314080 c l x0)). Qed.
Lemma lem5314084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5314085 (c : real) (l : real) : (term164 l c) = (term458 c l).
Proof. exact (MK_COMB (@lem5314084) (@lem5314004 c l)). Qed.
Lemma lem5314086 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term601 s x0 l c) = (term623 s c l x0).
Proof. exact (MK_COMB (@lem5314085 c l) (@lem5314083 s c l x0)). Qed.
Lemma lem5314088 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5314089 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term604 s x0 l c) = (term624 s c l x0).
Proof. exact (MK_COMB (@lem5314088 s) (@lem5314086 s c l x0)). Qed.
Lemma lem5314122 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term589 s x0 l c) = (term624 s c l x0).
Proof. exact (TRANS (@lem5313984 s x0 l c) (@lem5314089 s c l x0)). Qed.
Lemma lem5314126 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term624 s c l x0.
Proof. exact (h1). Qed.
Lemma lem5314127 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term623 s c l x0.
Proof. exact (proj2 (@lem5314126 s c l x0 h1)). Qed.
Lemma lem5314129 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term622 s c l x0.
Proof. exact (proj2 (@lem5314127 s c l x0 h1)). Qed.
Lemma lem5314130 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term359 c l.
Proof. exact (proj1 (@lem5314127 s c l x0 h1)). Qed.
Lemma lem5314131 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term621 c l x0.
Proof. exact (proj2 (@lem5314129 s c l x0 h1)). Qed.
Lemma lem5314133 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term619 c l x0.
Proof. exact (proj2 (@lem5314131 s c l x0 h1)). Qed.
Lemma lem5314134 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term609 c x0.
Proof. exact (proj1 (@lem5314131 s c l x0 h1)). Qed.
Lemma lem5314136 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5314137 : term461 = term431.
Proof. exact (@lem5314136 term358 term392). Qed.
Lemma lem5314139 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314140 : term392 = term421.
Proof. exact (@lem5314139 term386). Qed.
Lemma lem5314142 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314143 : term358 = term462.
Proof. exact (@lem5314142 (NUMERAL 0)). Qed.
Lemma lem5314144 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314145 : term463 = term464.
Proof. exact (MK_COMB (@lem5314144) (@lem5314143)). Qed.
Lemma lem5314146 : term431 = term465.
Proof. exact (MK_COMB (@lem5314145) (@lem5314140)). Qed.
Lemma lem5314147 : term466.
Proof. exact (@lem1980255 term358 term392 term392 term392). Qed.
Lemma lem5314149 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314150 : term431 = term432.
Proof. exact (@lem5314149 (NUMERAL 0) term386). Qed.
Lemma lem5314151 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314152 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314153 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314152 h1) (fun h1 : term432 = True => @lem5314151)). Qed.
Lemma lem5314154 : term432 = True.
Proof. exact (EQ_MP (@lem5314153) (@lem5314151)). Qed.
Lemma lem5314155 : term431 = True.
Proof. exact (TRANS (@lem5314150) (@lem5314154)). Qed.
Lemma lem5314156 : True = term431.
Proof. exact (SYM (@lem5314155)). Qed.
Lemma lem5314157 : term431.
Proof. exact (EQ_MP (@lem5314156) (@lem0)). Qed.
Lemma lem5314158 : term467.
Proof. exact (@lem5314147 (@lem5314157)). Qed.
Lemma lem5314160 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314161 : term431 = term432.
Proof. exact (@lem5314160 (NUMERAL 0) term386). Qed.
Lemma lem5314162 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314163 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314164 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314163 h1) (fun h1 : term432 = True => @lem5314162)). Qed.
Lemma lem5314165 : term432 = True.
Proof. exact (EQ_MP (@lem5314164) (@lem5314162)). Qed.
Lemma lem5314166 : term431 = True.
Proof. exact (TRANS (@lem5314161) (@lem5314165)). Qed.
Lemma lem5314167 : True = term431.
Proof. exact (SYM (@lem5314166)). Qed.
Lemma lem5314168 : term431.
Proof. exact (EQ_MP (@lem5314167) (@lem0)). Qed.
Lemma lem5314169 : term465 = term468.
Proof. exact (@lem5314158 (@lem5314168)). Qed.
Lemma lem5314171 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314172 : term469 = term406.
Proof. exact (@lem5314171 term386 term386). Qed.
Lemma lem5314173 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314174 : term405 = term386.
Proof. exact (EQ_MP (@lem5314173) (@lem940073)). Qed.
Lemma lem5314175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314176 : term406 = term392.
Proof. exact (MK_COMB (@lem5314175) (@lem5314174)). Qed.
Lemma lem5314177 : term469 = term392.
Proof. exact (TRANS (@lem5314172) (@lem5314176)). Qed.
Lemma lem5314179 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314180 : term471 = term358.
Proof. exact (@lem5314179 term386). Qed.
Lemma lem5314181 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314182 : term472 = term463.
Proof. exact (MK_COMB (@lem5314181) (@lem5314180)). Qed.
Lemma lem5314183 : term468 = term431.
Proof. exact (MK_COMB (@lem5314182) (@lem5314177)). Qed.
Lemma lem5314185 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314186 : term431 = term432.
Proof. exact (@lem5314185 (NUMERAL 0) term386). Qed.
Lemma lem5314187 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314188 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314189 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314188 h1) (fun h1 : term432 = True => @lem5314187)). Qed.
Lemma lem5314190 : term432 = True.
Proof. exact (EQ_MP (@lem5314189) (@lem5314187)). Qed.
Lemma lem5314191 : term431 = True.
Proof. exact (TRANS (@lem5314186) (@lem5314190)). Qed.
Lemma lem5314192 : term468 = True.
Proof. exact (TRANS (@lem5314183) (@lem5314191)). Qed.
Lemma lem5314193 : term465 = True.
Proof. exact (TRANS (@lem5314169) (@lem5314192)). Qed.
Lemma lem5314194 : term431 = True.
Proof. exact (TRANS (@lem5314146) (@lem5314193)). Qed.
Lemma lem5314195 : term461 = True.
Proof. exact (TRANS (@lem5314137) (@lem5314194)). Qed.
Lemma lem5314196 : True = term461.
Proof. exact (SYM (@lem5314195)). Qed.
Lemma lem5314197 : term461.
Proof. exact (EQ_MP (@lem5314196) (@lem0)). Qed.
Lemma lem5314198 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term625 c x0.
Proof. exact (conj (@lem5314197) (@lem5314134 s c l x0 h1)). Qed.
Lemma lem5314200 (x : real) (y : real) : term474 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5314201 (c : real) (x0 : real) : term626 c x0.
Proof. exact (@lem5314200 term392 (term606 c x0)). Qed.
Lemma lem5314202 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term627 c x0.
Proof. exact (@lem5314201 c x0 (@lem5314198 s c l x0 h1)). Qed.
Lemma lem5314203 (c : real) (x0 : real) : (term628 c x0) = (term606 c x0).
Proof. exact (@lem1982733 (term606 c x0)). Qed.
Lemma lem5314204 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5314205 (c : real) (x0 : real) : (term629 c x0) = (term608 c x0).
Proof. exact (MK_COMB (@lem5314204) (@lem5314203 c x0)). Qed.
Lemma lem5314206 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314207 (c : real) (x0 : real) : (term627 c x0) = (term609 c x0).
Proof. exact (MK_COMB (@lem5314205 c x0) (@lem5314206)). Qed.
Lemma lem5314208 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term609 c x0.
Proof. exact (EQ_MP (@lem5314207 c x0) (@lem5314202 s c l x0 h1)). Qed.
Lemma lem5314210 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5314211 : term461 = term431.
Proof. exact (@lem5314210 term358 term392). Qed.
Lemma lem5314213 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314214 : term392 = term421.
Proof. exact (@lem5314213 term386). Qed.
Lemma lem5314216 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314217 : term358 = term462.
Proof. exact (@lem5314216 (NUMERAL 0)). Qed.
Lemma lem5314218 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314219 : term463 = term464.
Proof. exact (MK_COMB (@lem5314218) (@lem5314217)). Qed.
Lemma lem5314220 : term431 = term465.
Proof. exact (MK_COMB (@lem5314219) (@lem5314214)). Qed.
Lemma lem5314221 : term466.
Proof. exact (@lem1980255 term358 term392 term392 term392). Qed.
Lemma lem5314223 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314224 : term431 = term432.
Proof. exact (@lem5314223 (NUMERAL 0) term386). Qed.
Lemma lem5314225 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314226 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314227 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314226 h1) (fun h1 : term432 = True => @lem5314225)). Qed.
Lemma lem5314228 : term432 = True.
Proof. exact (EQ_MP (@lem5314227) (@lem5314225)). Qed.
Lemma lem5314229 : term431 = True.
Proof. exact (TRANS (@lem5314224) (@lem5314228)). Qed.
Lemma lem5314230 : True = term431.
Proof. exact (SYM (@lem5314229)). Qed.
Lemma lem5314231 : term431.
Proof. exact (EQ_MP (@lem5314230) (@lem0)). Qed.
Lemma lem5314232 : term467.
Proof. exact (@lem5314221 (@lem5314231)). Qed.
Lemma lem5314234 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314235 : term431 = term432.
Proof. exact (@lem5314234 (NUMERAL 0) term386). Qed.
Lemma lem5314236 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314237 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314238 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314237 h1) (fun h1 : term432 = True => @lem5314236)). Qed.
Lemma lem5314239 : term432 = True.
Proof. exact (EQ_MP (@lem5314238) (@lem5314236)). Qed.
Lemma lem5314240 : term431 = True.
Proof. exact (TRANS (@lem5314235) (@lem5314239)). Qed.
Lemma lem5314241 : True = term431.
Proof. exact (SYM (@lem5314240)). Qed.
Lemma lem5314242 : term431.
Proof. exact (EQ_MP (@lem5314241) (@lem0)). Qed.
Lemma lem5314243 : term465 = term468.
Proof. exact (@lem5314232 (@lem5314242)). Qed.
Lemma lem5314245 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314246 : term469 = term406.
Proof. exact (@lem5314245 term386 term386). Qed.
Lemma lem5314247 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314248 : term405 = term386.
Proof. exact (EQ_MP (@lem5314247) (@lem940073)). Qed.
Lemma lem5314249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314250 : term406 = term392.
Proof. exact (MK_COMB (@lem5314249) (@lem5314248)). Qed.
Lemma lem5314251 : term469 = term392.
Proof. exact (TRANS (@lem5314246) (@lem5314250)). Qed.
Lemma lem5314253 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314254 : term471 = term358.
Proof. exact (@lem5314253 term386). Qed.
Lemma lem5314255 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314256 : term472 = term463.
Proof. exact (MK_COMB (@lem5314255) (@lem5314254)). Qed.
Lemma lem5314257 : term468 = term431.
Proof. exact (MK_COMB (@lem5314256) (@lem5314251)). Qed.
Lemma lem5314259 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314260 : term431 = term432.
Proof. exact (@lem5314259 (NUMERAL 0) term386). Qed.
Lemma lem5314261 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314262 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314263 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314262 h1) (fun h1 : term432 = True => @lem5314261)). Qed.
Lemma lem5314264 : term432 = True.
Proof. exact (EQ_MP (@lem5314263) (@lem5314261)). Qed.
Lemma lem5314265 : term431 = True.
Proof. exact (TRANS (@lem5314260) (@lem5314264)). Qed.
Lemma lem5314266 : term468 = True.
Proof. exact (TRANS (@lem5314257) (@lem5314265)). Qed.
Lemma lem5314267 : term465 = True.
Proof. exact (TRANS (@lem5314243) (@lem5314266)). Qed.
Lemma lem5314268 : term431 = True.
Proof. exact (TRANS (@lem5314220) (@lem5314267)). Qed.
Lemma lem5314269 : term461 = True.
Proof. exact (TRANS (@lem5314211) (@lem5314268)). Qed.
Lemma lem5314270 : True = term461.
Proof. exact (SYM (@lem5314269)). Qed.
Lemma lem5314271 : term461.
Proof. exact (EQ_MP (@lem5314270) (@lem0)). Qed.
Lemma lem5314272 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term630 c l x0.
Proof. exact (conj (@lem5314271) (@lem5314133 s c l x0 h1)). Qed.
Lemma lem5314274 (x : real) (y : real) : term488 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5314275 (c : real) (l : real) (x0 : real) : term631 c l x0.
Proof. exact (@lem5314274 term392 (term616 c l x0)). Qed.
Lemma lem5314276 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term632 c l x0.
Proof. exact (@lem5314275 c l x0 (@lem5314272 s c l x0 h1)). Qed.
Lemma lem5314277 (c : real) (l : real) (x0 : real) : (term633 c l x0) = (term616 c l x0).
Proof. exact (@lem1982733 (term616 c l x0)). Qed.
Lemma lem5314278 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314279 (c : real) (l : real) (x0 : real) : (term634 c l x0) = (term618 c l x0).
Proof. exact (MK_COMB (@lem5314278) (@lem5314277 c l x0)). Qed.
Lemma lem5314280 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314281 (c : real) (l : real) (x0 : real) : (term632 c l x0) = (term619 c l x0).
Proof. exact (MK_COMB (@lem5314279 c l x0) (@lem5314280)). Qed.
Lemma lem5314282 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term619 c l x0.
Proof. exact (EQ_MP (@lem5314281 c l x0) (@lem5314276 s c l x0 h1)). Qed.
Lemma lem5314284 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5314285 : term479 = term480.
Proof. exact (@lem5314284 term358 term368). Qed.
Lemma lem5314286 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem5314288 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314289 : term358 = term462.
Proof. exact (@lem5314288 (NUMERAL 0)). Qed.
Lemma lem5314290 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314291 : term463 = term464.
Proof. exact (MK_COMB (@lem5314290) (@lem5314289)). Qed.
Lemma lem5314292 : term480 = term481.
Proof. exact (MK_COMB (@lem5314291) (@lem5314286)). Qed.
Lemma lem5314293 : term482.
Proof. exact (@lem1980255 term358 term364 term392 term392). Qed.
Lemma lem5314295 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314296 : term431 = term432.
Proof. exact (@lem5314295 (NUMERAL 0) term386). Qed.
Lemma lem5314297 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314298 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314299 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314298 h1) (fun h1 : term432 = True => @lem5314297)). Qed.
Lemma lem5314300 : term432 = True.
Proof. exact (EQ_MP (@lem5314299) (@lem5314297)). Qed.
Lemma lem5314301 : term431 = True.
Proof. exact (TRANS (@lem5314296) (@lem5314300)). Qed.
Lemma lem5314302 : True = term431.
Proof. exact (SYM (@lem5314301)). Qed.
Lemma lem5314303 : term431.
Proof. exact (EQ_MP (@lem5314302) (@lem0)). Qed.
Lemma lem5314304 : term483.
Proof. exact (@lem5314293 (@lem5314303)). Qed.
Lemma lem5314306 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314307 : term427 = term428.
Proof. exact (@lem5314306 (NUMERAL 0) term369). Qed.
Lemma lem5314308 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5314309 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5314310 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5314309 h1) (fun h1 : term428 = True => @lem5314308)). Qed.
Lemma lem5314311 : term428 = True.
Proof. exact (EQ_MP (@lem5314310) (@lem5314308)). Qed.
Lemma lem5314312 : term427 = True.
Proof. exact (TRANS (@lem5314307) (@lem5314311)). Qed.
Lemma lem5314313 : True = term427.
Proof. exact (SYM (@lem5314312)). Qed.
Lemma lem5314314 : term427.
Proof. exact (EQ_MP (@lem5314313) (@lem0)). Qed.
Lemma lem5314315 : term481 = term484.
Proof. exact (@lem5314304 (@lem5314314)). Qed.
Lemma lem5314317 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314318 : term469 = term406.
Proof. exact (@lem5314317 term386 term386). Qed.
Lemma lem5314319 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314320 : term405 = term386.
Proof. exact (EQ_MP (@lem5314319) (@lem940073)). Qed.
Lemma lem5314321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314322 : term406 = term392.
Proof. exact (MK_COMB (@lem5314321) (@lem5314320)). Qed.
Lemma lem5314323 : term469 = term392.
Proof. exact (TRANS (@lem5314318) (@lem5314322)). Qed.
Lemma lem5314325 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314326 : term485 = term358.
Proof. exact (@lem5314325 term369). Qed.
Lemma lem5314327 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314328 : term486 = term463.
Proof. exact (MK_COMB (@lem5314327) (@lem5314326)). Qed.
Lemma lem5314329 : term484 = term431.
Proof. exact (MK_COMB (@lem5314328) (@lem5314323)). Qed.
Lemma lem5314331 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314332 : term431 = term432.
Proof. exact (@lem5314331 (NUMERAL 0) term386). Qed.
Lemma lem5314333 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314334 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314335 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314334 h1) (fun h1 : term432 = True => @lem5314333)). Qed.
Lemma lem5314336 : term432 = True.
Proof. exact (EQ_MP (@lem5314335) (@lem5314333)). Qed.
Lemma lem5314337 : term431 = True.
Proof. exact (TRANS (@lem5314332) (@lem5314336)). Qed.
Lemma lem5314338 : term484 = True.
Proof. exact (TRANS (@lem5314329) (@lem5314337)). Qed.
Lemma lem5314339 : term481 = True.
Proof. exact (TRANS (@lem5314315) (@lem5314338)). Qed.
Lemma lem5314340 : term480 = True.
Proof. exact (TRANS (@lem5314292) (@lem5314339)). Qed.
Lemma lem5314341 : term479 = True.
Proof. exact (TRANS (@lem5314285) (@lem5314340)). Qed.
Lemma lem5314342 : True = term479.
Proof. exact (SYM (@lem5314341)). Qed.
Lemma lem5314343 : term479.
Proof. exact (EQ_MP (@lem5314342) (@lem0)). Qed.
Lemma lem5314344 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term487 c l.
Proof. exact (conj (@lem5314343) (@lem5314130 s c l x0 h1)). Qed.
Lemma lem5314346 (x : real) (y : real) : term488 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5314347 (c : real) (l : real) : term489 c l.
Proof. exact (@lem5314346 term368 (term355 c l)). Qed.
Lemma lem5314348 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term490 c l.
Proof. exact (@lem5314347 c l (@lem5314344 s c l x0 h1)). Qed.
Lemma lem5314349 (c : real) (l : real) : (term491 c l) = (term492 c l).
Proof. exact (@lem1982781 c term368 (term493 l)). Qed.
Lemma lem5314350 (l : real) : (term494 l) = (term495 l).
Proof. exact (@lem1982749 term368 term380 l). Qed.
Lemma lem5314352 (x : nat) : (term383 x) = (term384 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5314353 : term380 = term385.
Proof. exact (@lem5314352 term386). Qed.
Lemma lem5314356 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5314357 : term496 = term497.
Proof. exact (MK_COMB (@lem5314356) (@lem5314353)). Qed.
Lemma lem5314358 : term497 = term498.
Proof. exact (@lem1981613 term392 term380 term364 term392). Qed.
Lemma lem5314360 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314361 : term447 = term448.
Proof. exact (@lem5314360 term369 term386). Qed.
Lemma lem5314362 : term449 = term398.
Proof. exact (@lem996237 term398). Qed.
Lemma lem5314363 : (term449 = term398) = (term450 = term369).
Proof. exact (@lem1007663 term398 (BIT1 0) term398). Qed.
Lemma lem5314364 : term450 = term369.
Proof. exact (EQ_MP (@lem5314363) (@lem5314362)). Qed.
Lemma lem5314365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314366 : term448 = term364.
Proof. exact (MK_COMB (@lem5314365) (@lem5314364)). Qed.
Lemma lem5314367 : term447 = term364.
Proof. exact (TRANS (@lem5314361) (@lem5314366)). Qed.
Lemma lem5314369 (m : nat) (n : nat) : (term499 m n) = (term401 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5314370 : term500 = term403.
Proof. exact (@lem5314369 term386 term386). Qed.
Lemma lem5314371 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314372 : term405 = term386.
Proof. exact (EQ_MP (@lem5314371) (@lem940073)). Qed.
Lemma lem5314373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314374 : term406 = term392.
Proof. exact (MK_COMB (@lem5314373) (@lem5314372)). Qed.
Lemma lem5314375 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5314376 : term403 = term380.
Proof. exact (MK_COMB (@lem5314375) (@lem5314374)). Qed.
Lemma lem5314377 : term500 = term380.
Proof. exact (TRANS (@lem5314370) (@lem5314376)). Qed.
Lemma lem5314378 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5314379 : term501 = term408.
Proof. exact (MK_COMB (@lem5314378) (@lem5314377)). Qed.
Lemma lem5314380 : term498 = term409.
Proof. exact (MK_COMB (@lem5314379) (@lem5314367)). Qed.
Lemma lem5314381 : term497 = term409.
Proof. exact (TRANS (@lem5314358) (@lem5314380)). Qed.
Lemma lem5314384 : term496 = term409.
Proof. exact (TRANS (@lem5314357) (@lem5314381)). Qed.
Lemma lem5314385 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314386 : term502 = term411.
Proof. exact (MK_COMB (@lem5314385) (@lem5314384)). Qed.
Lemma lem5314387 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5314388 (l : real) : (term495 l) = (term412 l).
Proof. exact (MK_COMB (@lem5314386) (@lem5314387 l)). Qed.
Lemma lem5314389 (l : real) : (term494 l) = (term412 l).
Proof. exact (TRANS (@lem5314350 l) (@lem5314388 l)). Qed.
Lemma lem5314392 (c : real) : (term503 c) = (term503 c).
Proof. exact (eq_refl (term503 c)). Qed.
Lemma lem5314393 (c : real) (l : real) : (term492 c l) = (term504 c l).
Proof. exact (MK_COMB (@lem5314392 c) (@lem5314389 l)). Qed.
Lemma lem5314394 (c : real) (l : real) : (term491 c l) = (term504 c l).
Proof. exact (TRANS (@lem5314349 c l) (@lem5314393 c l)). Qed.
Lemma lem5314395 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314396 (c : real) (l : real) : (term505 c l) = (term506 c l).
Proof. exact (MK_COMB (@lem5314395) (@lem5314394 c l)). Qed.
Lemma lem5314397 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314398 (c : real) (l : real) : (term490 c l) = (term507 c l).
Proof. exact (MK_COMB (@lem5314396 c l) (@lem5314397)). Qed.
Lemma lem5314399 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term507 c l.
Proof. exact (EQ_MP (@lem5314398 c l) (@lem5314348 s c l x0 h1)). Qed.
Lemma lem5314400 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term635 c l x0.
Proof. exact (conj (@lem5314399 s c l x0 h1) (@lem5314282 s c l x0 h1)). Qed.
Lemma lem5314402 (x : real) (y : real) : term636 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem5314403 (c : real) (l : real) (x0 : real) : term637 c l x0.
Proof. exact (@lem5314402 (term504 c l) (term616 c l x0)). Qed.
Lemma lem5314404 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term638 c l x0.
Proof. exact (@lem5314403 c l x0 (@lem5314400 s c l x0 h1)). Qed.
Lemma lem5314405 (c : real) (l : real) (x0 : real) : (term639 c l x0) = (term640 c l x0).
Proof. exact (@lem1982753 (term379 c) (term379 c) (term412 l) (term641 l x0)). Qed.
Lemma lem5314406 (c : real) : (term642 c) = (term643 c).
Proof. exact (@lem1982711 term368 term368 c). Qed.
Lemma lem5314412 : term644.
Proof. exact (@lem1981473 term392 term364 term392 term364 term392 term392). Qed.
Lemma lem5314414 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314415 : term427 = term428.
Proof. exact (@lem5314414 (NUMERAL 0) term369). Qed.
Lemma lem5314416 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5314417 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5314418 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5314417 h1) (fun h1 : term428 = True => @lem5314416)). Qed.
Lemma lem5314419 : term428 = True.
Proof. exact (EQ_MP (@lem5314418) (@lem5314416)). Qed.
Lemma lem5314420 : term427 = True.
Proof. exact (TRANS (@lem5314415) (@lem5314419)). Qed.
Lemma lem5314421 : True = term427.
Proof. exact (SYM (@lem5314420)). Qed.
Lemma lem5314422 : term427.
Proof. exact (EQ_MP (@lem5314421) (@lem0)). Qed.
Lemma lem5314423 : term645.
Proof. exact (@lem5314412 (@lem5314422)). Qed.
Lemma lem5314425 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314426 : term427 = term428.
Proof. exact (@lem5314425 (NUMERAL 0) term369). Qed.
Lemma lem5314427 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5314428 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5314429 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5314428 h1) (fun h1 : term428 = True => @lem5314427)). Qed.
Lemma lem5314430 : term428 = True.
Proof. exact (EQ_MP (@lem5314429) (@lem5314427)). Qed.
Lemma lem5314431 : term427 = True.
Proof. exact (TRANS (@lem5314426) (@lem5314430)). Qed.
Lemma lem5314432 : True = term427.
Proof. exact (SYM (@lem5314431)). Qed.
Lemma lem5314433 : term427.
Proof. exact (EQ_MP (@lem5314432) (@lem0)). Qed.
Lemma lem5314434 : term646.
Proof. exact (@lem5314423 (@lem5314433)). Qed.
Lemma lem5314436 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314437 : term431 = term432.
Proof. exact (@lem5314436 (NUMERAL 0) term386). Qed.
Lemma lem5314438 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314439 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314440 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314439 h1) (fun h1 : term432 = True => @lem5314438)). Qed.
Lemma lem5314441 : term432 = True.
Proof. exact (EQ_MP (@lem5314440) (@lem5314438)). Qed.
Lemma lem5314442 : term431 = True.
Proof. exact (TRANS (@lem5314437) (@lem5314441)). Qed.
Lemma lem5314443 : True = term431.
Proof. exact (SYM (@lem5314442)). Qed.
Lemma lem5314444 : term431.
Proof. exact (EQ_MP (@lem5314443) (@lem0)). Qed.
Lemma lem5314445 : term647.
Proof. exact (@lem5314434 (@lem5314444)). Qed.
Lemma lem5314447 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314448 : term395 = term396.
Proof. exact (@lem5314447 term386 term369). Qed.
Lemma lem5314449 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5314450 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5314451 : term399 = term369.
Proof. exact (EQ_MP (@lem5314450) (@lem5314449)). Qed.
Lemma lem5314452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314453 : term396 = term364.
Proof. exact (MK_COMB (@lem5314452) (@lem5314451)). Qed.
Lemma lem5314454 : term395 = term364.
Proof. exact (TRANS (@lem5314448) (@lem5314453)). Qed.
Lemma lem5314456 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314457 : term395 = term396.
Proof. exact (@lem5314456 term386 term369). Qed.
Lemma lem5314458 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5314459 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5314460 : term399 = term369.
Proof. exact (EQ_MP (@lem5314459) (@lem5314458)). Qed.
Lemma lem5314461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314462 : term396 = term364.
Proof. exact (MK_COMB (@lem5314461) (@lem5314460)). Qed.
Lemma lem5314463 : term395 = term364.
Proof. exact (TRANS (@lem5314457) (@lem5314462)). Qed.
Lemma lem5314464 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314465 : term523 = term524.
Proof. exact (MK_COMB (@lem5314464) (@lem5314463)). Qed.
Lemma lem5314466 : term648 = term649.
Proof. exact (MK_COMB (@lem5314465) (@lem5314454)). Qed.
Lemma lem5314467 : term649 = term650.
Proof. exact (@lem1367770 term369 term369). Qed.
Lemma lem5314468 : term651 = term534.
Proof. exact (@lem706951). Qed.
Lemma lem5314469 : (term651 = term534) = (term652 = term536).
Proof. exact (@lem1006570 term398 term398 term534). Qed.
Lemma lem5314470 : term652 = term536.
Proof. exact (EQ_MP (@lem5314469) (@lem5314468)). Qed.
Lemma lem5314471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314472 : term650 = term537.
Proof. exact (MK_COMB (@lem5314471) (@lem5314470)). Qed.
Lemma lem5314473 : term649 = term537.
Proof. exact (TRANS (@lem5314467) (@lem5314472)). Qed.
Lemma lem5314474 : term648 = term537.
Proof. exact (TRANS (@lem5314466) (@lem5314473)). Qed.
Lemma lem5314475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314476 : term653 = term654.
Proof. exact (MK_COMB (@lem5314475) (@lem5314474)). Qed.
Lemma lem5314477 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem5314478 : term655 = term656.
Proof. exact (MK_COMB (@lem5314476) (@lem5314477)). Qed.
Lemma lem5314480 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314481 : term656 = term657.
Proof. exact (@lem5314480 term536 term386). Qed.
Lemma lem5314482 : term658 = term534.
Proof. exact (@lem996237 term534). Qed.
Lemma lem5314483 : (term658 = term534) = (term659 = term536).
Proof. exact (@lem1007663 term534 (BIT1 0) term534). Qed.
Lemma lem5314484 : term659 = term536.
Proof. exact (EQ_MP (@lem5314483) (@lem5314482)). Qed.
Lemma lem5314485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314486 : term657 = term537.
Proof. exact (MK_COMB (@lem5314485) (@lem5314484)). Qed.
Lemma lem5314487 : term656 = term537.
Proof. exact (TRANS (@lem5314481) (@lem5314486)). Qed.
Lemma lem5314488 : term655 = term537.
Proof. exact (TRANS (@lem5314478) (@lem5314487)). Qed.
Lemma lem5314490 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314491 : term531 = term532.
Proof. exact (@lem5314490 term369 term369). Qed.
Lemma lem5314492 : (term404 = (BIT1 0)) = (term533 = term534).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314493 : term533 = term534.
Proof. exact (EQ_MP (@lem5314492) (@lem940073)). Qed.
Lemma lem5314494 : (term533 = term534) = (term535 = term536).
Proof. exact (@lem1008952 term398 term534). Qed.
Lemma lem5314495 : term535 = term536.
Proof. exact (EQ_MP (@lem5314494) (@lem5314493)). Qed.
Lemma lem5314496 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314497 : term532 = term537.
Proof. exact (MK_COMB (@lem5314496) (@lem5314495)). Qed.
Lemma lem5314498 : term531 = term537.
Proof. exact (TRANS (@lem5314491) (@lem5314497)). Qed.
Lemma lem5314499 : term445 = term445.
Proof. exact (eq_refl term445). Qed.
Lemma lem5314500 : term660 = term661.
Proof. exact (MK_COMB (@lem5314499) (@lem5314498)). Qed.
Lemma lem5314502 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314503 : term661 = term662.
Proof. exact (@lem5314502 term386 term536). Qed.
Lemma lem5314504 : term663 = term534.
Proof. exact (@lem996238 term534). Qed.
Lemma lem5314505 : (term663 = term534) = (term664 = term536).
Proof. exact (@lem1007663 (BIT1 0) term534 term534). Qed.
Lemma lem5314506 : term664 = term536.
Proof. exact (EQ_MP (@lem5314505) (@lem5314504)). Qed.
Lemma lem5314507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314508 : term662 = term537.
Proof. exact (MK_COMB (@lem5314507) (@lem5314506)). Qed.
Lemma lem5314509 : term661 = term537.
Proof. exact (TRANS (@lem5314503) (@lem5314508)). Qed.
Lemma lem5314510 : term660 = term537.
Proof. exact (TRANS (@lem5314500) (@lem5314509)). Qed.
Lemma lem5314511 : term537 = term660.
Proof. exact (SYM (@lem5314510)). Qed.
Lemma lem5314512 : term655 = term660.
Proof. exact (TRANS (@lem5314488) (@lem5314511)). Qed.
Lemma lem5314514 : term665 = term421.
Proof. exact (@lem5314445 (@lem5314512)). Qed.
Lemma lem5314516 (x : real) : (term541 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5314517 : term421 = term392.
Proof. exact (@lem5314516 term392). Qed.
Lemma lem5314518 : term665 = term392.
Proof. exact (TRANS (@lem5314514) (@lem5314517)). Qed.
Lemma lem5314519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314520 : term666 = term445.
Proof. exact (MK_COMB (@lem5314519) (@lem5314518)). Qed.
Lemma lem5314521 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5314522 (c : real) : (term643 c) = (term667 c).
Proof. exact (MK_COMB (@lem5314520) (@lem5314521 c)). Qed.
Lemma lem5314523 (c : real) : (term642 c) = (term667 c).
Proof. exact (TRANS (@lem5314406 c) (@lem5314522 c)). Qed.
Lemma lem5314524 (c : real) : (term667 c) = c.
Proof. exact (@lem1982709 c). Qed.
Lemma lem5314525 (c : real) : (term642 c) = c.
Proof. exact (TRANS (@lem5314523 c) (@lem5314524 c)). Qed.
Lemma lem5314526 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314527 (c : real) : (term668 c) = (real_add c).
Proof. exact (MK_COMB (@lem5314526) (@lem5314525 c)). Qed.
Lemma lem5314528 (l : real) (x0 : real) : (term669 l x0) = (term670 l x0).
Proof. exact (@lem1982763 (term412 l) (term379 l) (term493 x0)). Qed.
Lemma lem5314529 (l : real) : (term546 l) = (term547 l).
Proof. exact (@lem1982711 term409 term368 l). Qed.
Lemma lem5314535 : term548.
Proof. exact (@lem1981473 term380 term364 term392 term364 term358 term392). Qed.
Lemma lem5314537 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314538 : term427 = term428.
Proof. exact (@lem5314537 (NUMERAL 0) term369). Qed.
Lemma lem5314539 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5314540 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5314541 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5314540 h1) (fun h1 : term428 = True => @lem5314539)). Qed.
Lemma lem5314542 : term428 = True.
Proof. exact (EQ_MP (@lem5314541) (@lem5314539)). Qed.
Lemma lem5314543 : term427 = True.
Proof. exact (TRANS (@lem5314538) (@lem5314542)). Qed.
Lemma lem5314544 : True = term427.
Proof. exact (SYM (@lem5314543)). Qed.
Lemma lem5314545 : term427.
Proof. exact (EQ_MP (@lem5314544) (@lem0)). Qed.
Lemma lem5314546 : term549.
Proof. exact (@lem5314535 (@lem5314545)). Qed.
Lemma lem5314548 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314549 : term427 = term428.
Proof. exact (@lem5314548 (NUMERAL 0) term369). Qed.
Lemma lem5314550 : term429 = term398.
Proof. exact (@lem912803). Qed.
Lemma lem5314551 (h1 : term429 = term398) : term428 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term398 h1). Qed.
Lemma lem5314552 : (term429 = term398) = (term428 = True).
Proof. exact (prop_ext (fun h1 : term429 = term398 => @lem5314551 h1) (fun h1 : term428 = True => @lem5314550)). Qed.
Lemma lem5314553 : term428 = True.
Proof. exact (EQ_MP (@lem5314552) (@lem5314550)). Qed.
Lemma lem5314554 : term427 = True.
Proof. exact (TRANS (@lem5314549) (@lem5314553)). Qed.
Lemma lem5314555 : True = term427.
Proof. exact (SYM (@lem5314554)). Qed.
Lemma lem5314556 : term427.
Proof. exact (EQ_MP (@lem5314555) (@lem0)). Qed.
Lemma lem5314557 : term550.
Proof. exact (@lem5314546 (@lem5314556)). Qed.
Lemma lem5314559 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314560 : term431 = term432.
Proof. exact (@lem5314559 (NUMERAL 0) term386). Qed.
Lemma lem5314561 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314562 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314563 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314562 h1) (fun h1 : term432 = True => @lem5314561)). Qed.
Lemma lem5314564 : term432 = True.
Proof. exact (EQ_MP (@lem5314563) (@lem5314561)). Qed.
Lemma lem5314565 : term431 = True.
Proof. exact (TRANS (@lem5314560) (@lem5314564)). Qed.
Lemma lem5314566 : True = term431.
Proof. exact (SYM (@lem5314565)). Qed.
Lemma lem5314567 : term431.
Proof. exact (EQ_MP (@lem5314566) (@lem0)). Qed.
Lemma lem5314568 : term551.
Proof. exact (@lem5314557 (@lem5314567)). Qed.
Lemma lem5314570 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314571 : term395 = term396.
Proof. exact (@lem5314570 term386 term369). Qed.
Lemma lem5314572 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5314573 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5314574 : term399 = term369.
Proof. exact (EQ_MP (@lem5314573) (@lem5314572)). Qed.
Lemma lem5314575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314576 : term396 = term364.
Proof. exact (MK_COMB (@lem5314575) (@lem5314574)). Qed.
Lemma lem5314577 : term395 = term364.
Proof. exact (TRANS (@lem5314571) (@lem5314576)). Qed.
Lemma lem5314579 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5314580 : term520 = term521.
Proof. exact (@lem5314579 term386 term369). Qed.
Lemma lem5314581 : term397 = term398.
Proof. exact (@lem996238 term398). Qed.
Lemma lem5314582 : (term397 = term398) = (term399 = term369).
Proof. exact (@lem1007663 (BIT1 0) term398 term398). Qed.
Lemma lem5314583 : term399 = term369.
Proof. exact (EQ_MP (@lem5314582) (@lem5314581)). Qed.
Lemma lem5314584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314585 : term396 = term364.
Proof. exact (MK_COMB (@lem5314584) (@lem5314583)). Qed.
Lemma lem5314586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5314587 : term521 = term522.
Proof. exact (MK_COMB (@lem5314586) (@lem5314585)). Qed.
Lemma lem5314588 : term520 = term522.
Proof. exact (TRANS (@lem5314580) (@lem5314587)). Qed.
Lemma lem5314589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314590 : term552 = term553.
Proof. exact (MK_COMB (@lem5314589) (@lem5314588)). Qed.
Lemma lem5314591 : term554 = term555.
Proof. exact (MK_COMB (@lem5314590) (@lem5314577)). Qed.
Lemma lem5314593 (m : nat) : (term556 m) = term358.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5314594 : term555 = term358.
Proof. exact (@lem5314593 term369). Qed.
Lemma lem5314595 : term554 = term358.
Proof. exact (TRANS (@lem5314591) (@lem5314594)). Qed.
Lemma lem5314596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314597 : term557 = term529.
Proof. exact (MK_COMB (@lem5314596) (@lem5314595)). Qed.
Lemma lem5314598 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem5314599 : term558 = term471.
Proof. exact (MK_COMB (@lem5314597) (@lem5314598)). Qed.
Lemma lem5314601 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314602 : term471 = term358.
Proof. exact (@lem5314601 term386). Qed.
Lemma lem5314603 : term558 = term358.
Proof. exact (TRANS (@lem5314599) (@lem5314602)). Qed.
Lemma lem5314605 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314606 : term531 = term532.
Proof. exact (@lem5314605 term369 term369). Qed.
Lemma lem5314607 : (term404 = (BIT1 0)) = (term533 = term534).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314608 : term533 = term534.
Proof. exact (EQ_MP (@lem5314607) (@lem940073)). Qed.
Lemma lem5314609 : (term533 = term534) = (term535 = term536).
Proof. exact (@lem1008952 term398 term534). Qed.
Lemma lem5314610 : term535 = term536.
Proof. exact (EQ_MP (@lem5314609) (@lem5314608)). Qed.
Lemma lem5314611 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314612 : term532 = term537.
Proof. exact (MK_COMB (@lem5314611) (@lem5314610)). Qed.
Lemma lem5314613 : term531 = term537.
Proof. exact (TRANS (@lem5314606) (@lem5314612)). Qed.
Lemma lem5314614 : term529 = term529.
Proof. exact (eq_refl term529). Qed.
Lemma lem5314615 : term538 = term539.
Proof. exact (MK_COMB (@lem5314614) (@lem5314613)). Qed.
Lemma lem5314617 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314618 : term539 = term358.
Proof. exact (@lem5314617 term536). Qed.
Lemma lem5314619 : term538 = term358.
Proof. exact (TRANS (@lem5314615) (@lem5314618)). Qed.
Lemma lem5314620 : term358 = term538.
Proof. exact (SYM (@lem5314619)). Qed.
Lemma lem5314621 : term558 = term538.
Proof. exact (TRANS (@lem5314603) (@lem5314620)). Qed.
Lemma lem5314623 : term559 = term462.
Proof. exact (@lem5314568 (@lem5314621)). Qed.
Lemma lem5314625 (x : real) : (term541 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5314626 : term462 = term358.
Proof. exact (@lem5314625 term358). Qed.
Lemma lem5314627 : term559 = term358.
Proof. exact (TRANS (@lem5314623) (@lem5314626)). Qed.
Lemma lem5314628 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314629 : term560 = term529.
Proof. exact (MK_COMB (@lem5314628) (@lem5314627)). Qed.
Lemma lem5314630 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5314631 (l : real) : (term547 l) = (term543 l).
Proof. exact (MK_COMB (@lem5314629) (@lem5314630 l)). Qed.
Lemma lem5314632 (l : real) : (term546 l) = (term543 l).
Proof. exact (TRANS (@lem5314529 l) (@lem5314631 l)). Qed.
Lemma lem5314633 (l : real) : (term543 l) = term358.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5314634 (l : real) : (term546 l) = term358.
Proof. exact (TRANS (@lem5314632 l) (@lem5314633 l)). Qed.
Lemma lem5314635 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314636 (l : real) : (term671 l) = term545.
Proof. exact (MK_COMB (@lem5314635) (@lem5314634 l)). Qed.
Lemma lem5314637 (x0 : real) : (term493 x0) = (term493 x0).
Proof. exact (eq_refl (term493 x0)). Qed.
Lemma lem5314638 (l : real) (x0 : real) : (term670 l x0) = (term672 x0).
Proof. exact (MK_COMB (@lem5314636 l) (@lem5314637 x0)). Qed.
Lemma lem5314639 (l : real) (x0 : real) : (term669 l x0) = (term672 x0).
Proof. exact (TRANS (@lem5314528 l x0) (@lem5314638 l x0)). Qed.
Lemma lem5314640 (x0 : real) : (term672 x0) = (term493 x0).
Proof. exact (@lem1982721 (term493 x0)). Qed.
Lemma lem5314641 (l : real) (x0 : real) : (term669 l x0) = (term493 x0).
Proof. exact (TRANS (@lem5314639 l x0) (@lem5314640 x0)). Qed.
Lemma lem5314642 (l : real) (c : real) (x0 : real) : (term640 c l x0) = (term355 c x0).
Proof. exact (MK_COMB (@lem5314527 c) (@lem5314641 l x0)). Qed.
Lemma lem5314643 (l : real) (c : real) (x0 : real) : (term639 c l x0) = (term355 c x0).
Proof. exact (TRANS (@lem5314405 c l x0) (@lem5314642 l c x0)). Qed.
Lemma lem5314644 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314645 (l : real) (c : real) (x0 : real) : (term673 c l x0) = (term357 c x0).
Proof. exact (MK_COMB (@lem5314644) (@lem5314643 l c x0)). Qed.
Lemma lem5314646 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314647 (l : real) (c : real) (x0 : real) : (term638 c l x0) = (term359 c x0).
Proof. exact (MK_COMB (@lem5314645 l c x0) (@lem5314646)). Qed.
Lemma lem5314648 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term359 c x0.
Proof. exact (EQ_MP (@lem5314647 l c x0) (@lem5314404 s c l x0 h1)). Qed.
Lemma lem5314650 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5314651 : term461 = term431.
Proof. exact (@lem5314650 term358 term392). Qed.
Lemma lem5314653 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314654 : term392 = term421.
Proof. exact (@lem5314653 term386). Qed.
Lemma lem5314656 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314657 : term358 = term462.
Proof. exact (@lem5314656 (NUMERAL 0)). Qed.
Lemma lem5314658 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314659 : term463 = term464.
Proof. exact (MK_COMB (@lem5314658) (@lem5314657)). Qed.
Lemma lem5314660 : term431 = term465.
Proof. exact (MK_COMB (@lem5314659) (@lem5314654)). Qed.
Lemma lem5314661 : term466.
Proof. exact (@lem1980255 term358 term392 term392 term392). Qed.
Lemma lem5314663 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314664 : term431 = term432.
Proof. exact (@lem5314663 (NUMERAL 0) term386). Qed.
Lemma lem5314665 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314666 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314667 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314666 h1) (fun h1 : term432 = True => @lem5314665)). Qed.
Lemma lem5314668 : term432 = True.
Proof. exact (EQ_MP (@lem5314667) (@lem5314665)). Qed.
Lemma lem5314669 : term431 = True.
Proof. exact (TRANS (@lem5314664) (@lem5314668)). Qed.
Lemma lem5314670 : True = term431.
Proof. exact (SYM (@lem5314669)). Qed.
Lemma lem5314671 : term431.
Proof. exact (EQ_MP (@lem5314670) (@lem0)). Qed.
Lemma lem5314672 : term467.
Proof. exact (@lem5314661 (@lem5314671)). Qed.
Lemma lem5314674 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314675 : term431 = term432.
Proof. exact (@lem5314674 (NUMERAL 0) term386). Qed.
Lemma lem5314676 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314677 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314678 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314677 h1) (fun h1 : term432 = True => @lem5314676)). Qed.
Lemma lem5314679 : term432 = True.
Proof. exact (EQ_MP (@lem5314678) (@lem5314676)). Qed.
Lemma lem5314680 : term431 = True.
Proof. exact (TRANS (@lem5314675) (@lem5314679)). Qed.
Lemma lem5314681 : True = term431.
Proof. exact (SYM (@lem5314680)). Qed.
Lemma lem5314682 : term431.
Proof. exact (EQ_MP (@lem5314681) (@lem0)). Qed.
Lemma lem5314683 : term465 = term468.
Proof. exact (@lem5314672 (@lem5314682)). Qed.
Lemma lem5314685 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314686 : term469 = term406.
Proof. exact (@lem5314685 term386 term386). Qed.
Lemma lem5314687 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314688 : term405 = term386.
Proof. exact (EQ_MP (@lem5314687) (@lem940073)). Qed.
Lemma lem5314689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314690 : term406 = term392.
Proof. exact (MK_COMB (@lem5314689) (@lem5314688)). Qed.
Lemma lem5314691 : term469 = term392.
Proof. exact (TRANS (@lem5314686) (@lem5314690)). Qed.
Lemma lem5314693 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314694 : term471 = term358.
Proof. exact (@lem5314693 term386). Qed.
Lemma lem5314695 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314696 : term472 = term463.
Proof. exact (MK_COMB (@lem5314695) (@lem5314694)). Qed.
Lemma lem5314697 : term468 = term431.
Proof. exact (MK_COMB (@lem5314696) (@lem5314691)). Qed.
Lemma lem5314699 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314700 : term431 = term432.
Proof. exact (@lem5314699 (NUMERAL 0) term386). Qed.
Lemma lem5314701 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314702 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314703 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314702 h1) (fun h1 : term432 = True => @lem5314701)). Qed.
Lemma lem5314704 : term432 = True.
Proof. exact (EQ_MP (@lem5314703) (@lem5314701)). Qed.
Lemma lem5314705 : term431 = True.
Proof. exact (TRANS (@lem5314700) (@lem5314704)). Qed.
Lemma lem5314706 : term468 = True.
Proof. exact (TRANS (@lem5314697) (@lem5314705)). Qed.
Lemma lem5314707 : term465 = True.
Proof. exact (TRANS (@lem5314683) (@lem5314706)). Qed.
Lemma lem5314708 : term431 = True.
Proof. exact (TRANS (@lem5314660) (@lem5314707)). Qed.
Lemma lem5314709 : term461 = True.
Proof. exact (TRANS (@lem5314651) (@lem5314708)). Qed.
Lemma lem5314710 : True = term461.
Proof. exact (SYM (@lem5314709)). Qed.
Lemma lem5314711 : term461.
Proof. exact (EQ_MP (@lem5314710) (@lem0)). Qed.
Lemma lem5314712 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term674 c x0.
Proof. exact (conj (@lem5314711) (@lem5314648 s c l x0 h1)). Qed.
Lemma lem5314714 (x : real) (y : real) : term488 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5314715 (c : real) (x0 : real) : term675 c x0.
Proof. exact (@lem5314714 term392 (term355 c x0)). Qed.
Lemma lem5314716 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term676 c x0.
Proof. exact (@lem5314715 c x0 (@lem5314712 s c l x0 h1)). Qed.
Lemma lem5314717 (c : real) (x0 : real) : (term677 c x0) = (term355 c x0).
Proof. exact (@lem1982733 (term355 c x0)). Qed.
Lemma lem5314718 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314719 (c : real) (x0 : real) : (term678 c x0) = (term357 c x0).
Proof. exact (MK_COMB (@lem5314718) (@lem5314717 c x0)). Qed.
Lemma lem5314720 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314721 (c : real) (x0 : real) : (term676 c x0) = (term359 c x0).
Proof. exact (MK_COMB (@lem5314719 c x0) (@lem5314720)). Qed.
Lemma lem5314722 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term359 c x0.
Proof. exact (EQ_MP (@lem5314721 c x0) (@lem5314716 s c l x0 h1)). Qed.
Lemma lem5314723 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term679 c x0.
Proof. exact (conj (@lem5314722 s c l x0 h1) (@lem5314208 s c l x0 h1)). Qed.
Lemma lem5314725 (x : real) (y : real) : term509 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5314726 (c : real) (x0 : real) : term680 c x0.
Proof. exact (@lem5314725 (term355 c x0) (term606 c x0)). Qed.
Lemma lem5314727 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term681 c x0.
Proof. exact (@lem5314726 c x0 (@lem5314723 s c l x0 h1)). Qed.
Lemma lem5314728 (c : real) (x0 : real) : (term682 c x0) = (term683 c x0).
Proof. exact (@lem1982753 c (term493 c) (term493 x0) x0). Qed.
Lemma lem5314729 (c : real) : (term684 c) = (term685 c).
Proof. exact (@lem1982715 term380 c). Qed.
Lemma lem5314731 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314732 : term392 = term421.
Proof. exact (@lem5314731 term386). Qed.
Lemma lem5314734 (x : nat) : (term383 x) = (term384 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5314735 : term380 = term385.
Proof. exact (@lem5314734 term386). Qed.
Lemma lem5314736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314737 : term437 = term686.
Proof. exact (MK_COMB (@lem5314736) (@lem5314735)). Qed.
Lemma lem5314738 : term687 = term688.
Proof. exact (MK_COMB (@lem5314737) (@lem5314732)). Qed.
Lemma lem5314739 : term689.
Proof. exact (@lem1981473 term380 term392 term392 term392 term358 term392). Qed.
Lemma lem5314741 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314742 : term431 = term432.
Proof. exact (@lem5314741 (NUMERAL 0) term386). Qed.
Lemma lem5314743 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314744 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314745 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314744 h1) (fun h1 : term432 = True => @lem5314743)). Qed.
Lemma lem5314746 : term432 = True.
Proof. exact (EQ_MP (@lem5314745) (@lem5314743)). Qed.
Lemma lem5314747 : term431 = True.
Proof. exact (TRANS (@lem5314742) (@lem5314746)). Qed.
Lemma lem5314748 : True = term431.
Proof. exact (SYM (@lem5314747)). Qed.
Lemma lem5314749 : term431.
Proof. exact (EQ_MP (@lem5314748) (@lem0)). Qed.
Lemma lem5314750 : term690.
Proof. exact (@lem5314739 (@lem5314749)). Qed.
Lemma lem5314752 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314753 : term431 = term432.
Proof. exact (@lem5314752 (NUMERAL 0) term386). Qed.
Lemma lem5314754 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314755 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314756 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314755 h1) (fun h1 : term432 = True => @lem5314754)). Qed.
Lemma lem5314757 : term432 = True.
Proof. exact (EQ_MP (@lem5314756) (@lem5314754)). Qed.
Lemma lem5314758 : term431 = True.
Proof. exact (TRANS (@lem5314753) (@lem5314757)). Qed.
Lemma lem5314759 : True = term431.
Proof. exact (SYM (@lem5314758)). Qed.
Lemma lem5314760 : term431.
Proof. exact (EQ_MP (@lem5314759) (@lem0)). Qed.
Lemma lem5314761 : term691.
Proof. exact (@lem5314750 (@lem5314760)). Qed.
Lemma lem5314763 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314764 : term431 = term432.
Proof. exact (@lem5314763 (NUMERAL 0) term386). Qed.
Lemma lem5314765 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314766 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314767 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314766 h1) (fun h1 : term432 = True => @lem5314765)). Qed.
Lemma lem5314768 : term432 = True.
Proof. exact (EQ_MP (@lem5314767) (@lem5314765)). Qed.
Lemma lem5314769 : term431 = True.
Proof. exact (TRANS (@lem5314764) (@lem5314768)). Qed.
Lemma lem5314770 : True = term431.
Proof. exact (SYM (@lem5314769)). Qed.
Lemma lem5314771 : term431.
Proof. exact (EQ_MP (@lem5314770) (@lem0)). Qed.
Lemma lem5314772 : term692.
Proof. exact (@lem5314761 (@lem5314771)). Qed.
Lemma lem5314774 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314775 : term469 = term406.
Proof. exact (@lem5314774 term386 term386). Qed.
Lemma lem5314776 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314777 : term405 = term386.
Proof. exact (EQ_MP (@lem5314776) (@lem940073)). Qed.
Lemma lem5314778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314779 : term406 = term392.
Proof. exact (MK_COMB (@lem5314778) (@lem5314777)). Qed.
Lemma lem5314780 : term469 = term392.
Proof. exact (TRANS (@lem5314775) (@lem5314779)). Qed.
Lemma lem5314782 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5314783 : term402 = term403.
Proof. exact (@lem5314782 term386 term386). Qed.
Lemma lem5314784 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314785 : term405 = term386.
Proof. exact (EQ_MP (@lem5314784) (@lem940073)). Qed.
Lemma lem5314786 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314787 : term406 = term392.
Proof. exact (MK_COMB (@lem5314786) (@lem5314785)). Qed.
Lemma lem5314788 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5314789 : term403 = term380.
Proof. exact (MK_COMB (@lem5314788) (@lem5314787)). Qed.
Lemma lem5314790 : term402 = term380.
Proof. exact (TRANS (@lem5314783) (@lem5314789)). Qed.
Lemma lem5314791 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314792 : term436 = term437.
Proof. exact (MK_COMB (@lem5314791) (@lem5314790)). Qed.
Lemma lem5314793 : term693 = term687.
Proof. exact (MK_COMB (@lem5314792) (@lem5314780)). Qed.
Lemma lem5314795 (m : nat) : (term556 m) = term358.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5314796 : term687 = term358.
Proof. exact (@lem5314795 term386). Qed.
Lemma lem5314797 : term693 = term358.
Proof. exact (TRANS (@lem5314793) (@lem5314796)). Qed.
Lemma lem5314798 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314799 : term694 = term529.
Proof. exact (MK_COMB (@lem5314798) (@lem5314797)). Qed.
Lemma lem5314800 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem5314801 : term695 = term471.
Proof. exact (MK_COMB (@lem5314799) (@lem5314800)). Qed.
Lemma lem5314803 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314804 : term471 = term358.
Proof. exact (@lem5314803 term386). Qed.
Lemma lem5314805 : term695 = term358.
Proof. exact (TRANS (@lem5314801) (@lem5314804)). Qed.
Lemma lem5314807 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314808 : term469 = term406.
Proof. exact (@lem5314807 term386 term386). Qed.
Lemma lem5314809 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314810 : term405 = term386.
Proof. exact (EQ_MP (@lem5314809) (@lem940073)). Qed.
Lemma lem5314811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314812 : term406 = term392.
Proof. exact (MK_COMB (@lem5314811) (@lem5314810)). Qed.
Lemma lem5314813 : term469 = term392.
Proof. exact (TRANS (@lem5314808) (@lem5314812)). Qed.
Lemma lem5314814 : term529 = term529.
Proof. exact (eq_refl term529). Qed.
Lemma lem5314815 : term696 = term471.
Proof. exact (MK_COMB (@lem5314814) (@lem5314813)). Qed.
Lemma lem5314817 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314818 : term471 = term358.
Proof. exact (@lem5314817 term386). Qed.
Lemma lem5314819 : term696 = term358.
Proof. exact (TRANS (@lem5314815) (@lem5314818)). Qed.
Lemma lem5314820 : term358 = term696.
Proof. exact (SYM (@lem5314819)). Qed.
Lemma lem5314821 : term695 = term696.
Proof. exact (TRANS (@lem5314805) (@lem5314820)). Qed.
Lemma lem5314822 : term688 = term462.
Proof. exact (@lem5314772 (@lem5314821)). Qed.
Lemma lem5314823 : term687 = term462.
Proof. exact (TRANS (@lem5314738) (@lem5314822)). Qed.
Lemma lem5314825 (x : real) : (term541 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5314826 : term462 = term358.
Proof. exact (@lem5314825 term358). Qed.
Lemma lem5314827 : term687 = term358.
Proof. exact (TRANS (@lem5314823) (@lem5314826)). Qed.
Lemma lem5314828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314829 : term697 = term529.
Proof. exact (MK_COMB (@lem5314828) (@lem5314827)). Qed.
Lemma lem5314830 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5314831 (c : real) : (term685 c) = (term543 c).
Proof. exact (MK_COMB (@lem5314829) (@lem5314830 c)). Qed.
Lemma lem5314832 (c : real) : (term684 c) = (term543 c).
Proof. exact (TRANS (@lem5314729 c) (@lem5314831 c)). Qed.
Lemma lem5314833 (c : real) : (term543 c) = term358.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5314834 (c : real) : (term684 c) = term358.
Proof. exact (TRANS (@lem5314832 c) (@lem5314833 c)). Qed.
Lemma lem5314835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314836 (c : real) : (term698 c) = term545.
Proof. exact (MK_COMB (@lem5314835) (@lem5314834 c)). Qed.
Lemma lem5314837 (x0 : real) : (term699 x0) = (term685 x0).
Proof. exact (@lem1982713 term380 x0). Qed.
Lemma lem5314839 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314840 : term392 = term421.
Proof. exact (@lem5314839 term386). Qed.
Lemma lem5314842 (x : nat) : (term383 x) = (term384 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5314843 : term380 = term385.
Proof. exact (@lem5314842 term386). Qed.
Lemma lem5314844 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314845 : term437 = term686.
Proof. exact (MK_COMB (@lem5314844) (@lem5314843)). Qed.
Lemma lem5314846 : term687 = term688.
Proof. exact (MK_COMB (@lem5314845) (@lem5314840)). Qed.
Lemma lem5314847 : term689.
Proof. exact (@lem1981473 term380 term392 term392 term392 term358 term392). Qed.
Lemma lem5314849 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314850 : term431 = term432.
Proof. exact (@lem5314849 (NUMERAL 0) term386). Qed.
Lemma lem5314851 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314852 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314853 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314852 h1) (fun h1 : term432 = True => @lem5314851)). Qed.
Lemma lem5314854 : term432 = True.
Proof. exact (EQ_MP (@lem5314853) (@lem5314851)). Qed.
Lemma lem5314855 : term431 = True.
Proof. exact (TRANS (@lem5314850) (@lem5314854)). Qed.
Lemma lem5314856 : True = term431.
Proof. exact (SYM (@lem5314855)). Qed.
Lemma lem5314857 : term431.
Proof. exact (EQ_MP (@lem5314856) (@lem0)). Qed.
Lemma lem5314858 : term690.
Proof. exact (@lem5314847 (@lem5314857)). Qed.
Lemma lem5314860 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314861 : term431 = term432.
Proof. exact (@lem5314860 (NUMERAL 0) term386). Qed.
Lemma lem5314862 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314863 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314864 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314863 h1) (fun h1 : term432 = True => @lem5314862)). Qed.
Lemma lem5314865 : term432 = True.
Proof. exact (EQ_MP (@lem5314864) (@lem5314862)). Qed.
Lemma lem5314866 : term431 = True.
Proof. exact (TRANS (@lem5314861) (@lem5314865)). Qed.
Lemma lem5314867 : True = term431.
Proof. exact (SYM (@lem5314866)). Qed.
Lemma lem5314868 : term431.
Proof. exact (EQ_MP (@lem5314867) (@lem0)). Qed.
Lemma lem5314869 : term691.
Proof. exact (@lem5314858 (@lem5314868)). Qed.
Lemma lem5314871 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314872 : term431 = term432.
Proof. exact (@lem5314871 (NUMERAL 0) term386). Qed.
Lemma lem5314873 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314874 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314875 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314874 h1) (fun h1 : term432 = True => @lem5314873)). Qed.
Lemma lem5314876 : term432 = True.
Proof. exact (EQ_MP (@lem5314875) (@lem5314873)). Qed.
Lemma lem5314877 : term431 = True.
Proof. exact (TRANS (@lem5314872) (@lem5314876)). Qed.
Lemma lem5314878 : True = term431.
Proof. exact (SYM (@lem5314877)). Qed.
Lemma lem5314879 : term431.
Proof. exact (EQ_MP (@lem5314878) (@lem0)). Qed.
Lemma lem5314880 : term692.
Proof. exact (@lem5314869 (@lem5314879)). Qed.
Lemma lem5314882 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314883 : term469 = term406.
Proof. exact (@lem5314882 term386 term386). Qed.
Lemma lem5314884 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314885 : term405 = term386.
Proof. exact (EQ_MP (@lem5314884) (@lem940073)). Qed.
Lemma lem5314886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314887 : term406 = term392.
Proof. exact (MK_COMB (@lem5314886) (@lem5314885)). Qed.
Lemma lem5314888 : term469 = term392.
Proof. exact (TRANS (@lem5314883) (@lem5314887)). Qed.
Lemma lem5314890 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5314891 : term402 = term403.
Proof. exact (@lem5314890 term386 term386). Qed.
Lemma lem5314892 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314893 : term405 = term386.
Proof. exact (EQ_MP (@lem5314892) (@lem940073)). Qed.
Lemma lem5314894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314895 : term406 = term392.
Proof. exact (MK_COMB (@lem5314894) (@lem5314893)). Qed.
Lemma lem5314896 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5314897 : term403 = term380.
Proof. exact (MK_COMB (@lem5314896) (@lem5314895)). Qed.
Lemma lem5314898 : term402 = term380.
Proof. exact (TRANS (@lem5314891) (@lem5314897)). Qed.
Lemma lem5314899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5314900 : term436 = term437.
Proof. exact (MK_COMB (@lem5314899) (@lem5314898)). Qed.
Lemma lem5314901 : term693 = term687.
Proof. exact (MK_COMB (@lem5314900) (@lem5314888)). Qed.
Lemma lem5314903 (m : nat) : (term556 m) = term358.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5314904 : term687 = term358.
Proof. exact (@lem5314903 term386). Qed.
Lemma lem5314905 : term693 = term358.
Proof. exact (TRANS (@lem5314901) (@lem5314904)). Qed.
Lemma lem5314906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314907 : term694 = term529.
Proof. exact (MK_COMB (@lem5314906) (@lem5314905)). Qed.
Lemma lem5314908 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem5314909 : term695 = term471.
Proof. exact (MK_COMB (@lem5314907) (@lem5314908)). Qed.
Lemma lem5314911 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314912 : term471 = term358.
Proof. exact (@lem5314911 term386). Qed.
Lemma lem5314913 : term695 = term358.
Proof. exact (TRANS (@lem5314909) (@lem5314912)). Qed.
Lemma lem5314915 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5314916 : term469 = term406.
Proof. exact (@lem5314915 term386 term386). Qed.
Lemma lem5314917 : (term404 = (BIT1 0)) = (term405 = term386).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5314918 : term405 = term386.
Proof. exact (EQ_MP (@lem5314917) (@lem940073)). Qed.
Lemma lem5314919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5314920 : term406 = term392.
Proof. exact (MK_COMB (@lem5314919) (@lem5314918)). Qed.
Lemma lem5314921 : term469 = term392.
Proof. exact (TRANS (@lem5314916) (@lem5314920)). Qed.
Lemma lem5314922 : term529 = term529.
Proof. exact (eq_refl term529). Qed.
Lemma lem5314923 : term696 = term471.
Proof. exact (MK_COMB (@lem5314922) (@lem5314921)). Qed.
Lemma lem5314925 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314926 : term471 = term358.
Proof. exact (@lem5314925 term386). Qed.
Lemma lem5314927 : term696 = term358.
Proof. exact (TRANS (@lem5314923) (@lem5314926)). Qed.
Lemma lem5314928 : term358 = term696.
Proof. exact (SYM (@lem5314927)). Qed.
Lemma lem5314929 : term695 = term696.
Proof. exact (TRANS (@lem5314913) (@lem5314928)). Qed.
Lemma lem5314930 : term688 = term462.
Proof. exact (@lem5314880 (@lem5314929)). Qed.
Lemma lem5314931 : term687 = term462.
Proof. exact (TRANS (@lem5314846) (@lem5314930)). Qed.
Lemma lem5314933 (x : real) : (term541 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5314934 : term462 = term358.
Proof. exact (@lem5314933 term358). Qed.
Lemma lem5314935 : term687 = term358.
Proof. exact (TRANS (@lem5314931) (@lem5314934)). Qed.
Lemma lem5314936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5314937 : term697 = term529.
Proof. exact (MK_COMB (@lem5314936) (@lem5314935)). Qed.
Lemma lem5314938 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem5314939 (x0 : real) : (term685 x0) = (term543 x0).
Proof. exact (MK_COMB (@lem5314937) (@lem5314938 x0)). Qed.
Lemma lem5314940 (x0 : real) : (term699 x0) = (term543 x0).
Proof. exact (TRANS (@lem5314837 x0) (@lem5314939 x0)). Qed.
Lemma lem5314941 (x0 : real) : (term543 x0) = term358.
Proof. exact (@lem1982719 x0). Qed.
Lemma lem5314942 (x0 : real) : (term699 x0) = term358.
Proof. exact (TRANS (@lem5314940 x0) (@lem5314941 x0)). Qed.
Lemma lem5314943 (c : real) (x0 : real) : (term683 c x0) = term561.
Proof. exact (MK_COMB (@lem5314836 c) (@lem5314942 x0)). Qed.
Lemma lem5314944 (c : real) (x0 : real) : (term682 c x0) = term561.
Proof. exact (TRANS (@lem5314728 c x0) (@lem5314943 c x0)). Qed.
Lemma lem5314945 : term561 = term358.
Proof. exact (@lem1982721 term358). Qed.
Lemma lem5314946 (c : real) (x0 : real) : (term682 c x0) = term358.
Proof. exact (TRANS (@lem5314944 c x0) (@lem5314945)). Qed.
Lemma lem5314947 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5314948 (c : real) (x0 : real) : (term700 c x0) = term563.
Proof. exact (MK_COMB (@lem5314947) (@lem5314946 c x0)). Qed.
Lemma lem5314949 : term358 = term358.
Proof. exact (eq_refl term358). Qed.
Lemma lem5314950 (c : real) (x0 : real) : (term681 c x0) = term564.
Proof. exact (MK_COMB (@lem5314948 c x0) (@lem5314949)). Qed.
Lemma lem5314951 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term564.
Proof. exact (EQ_MP (@lem5314950 c x0) (@lem5314727 s c l x0 h1)). Qed.
Lemma lem5314953 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5314954 : term564 = term565.
Proof. exact (@lem5314953 term358 term358). Qed.
Lemma lem5314956 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314957 : term358 = term462.
Proof. exact (@lem5314956 (NUMERAL 0)). Qed.
Lemma lem5314959 (x : nat) : (real_of_num x) = (term420 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5314960 : term358 = term462.
Proof. exact (@lem5314959 (NUMERAL 0)). Qed.
Lemma lem5314961 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314962 : term463 = term464.
Proof. exact (MK_COMB (@lem5314961) (@lem5314960)). Qed.
Lemma lem5314963 : term565 = term566.
Proof. exact (MK_COMB (@lem5314962) (@lem5314957)). Qed.
Lemma lem5314964 : term567.
Proof. exact (@lem1980255 term358 term392 term358 term392). Qed.
Lemma lem5314966 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314967 : term431 = term432.
Proof. exact (@lem5314966 (NUMERAL 0) term386). Qed.
Lemma lem5314968 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314969 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314970 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314969 h1) (fun h1 : term432 = True => @lem5314968)). Qed.
Lemma lem5314971 : term432 = True.
Proof. exact (EQ_MP (@lem5314970) (@lem5314968)). Qed.
Lemma lem5314972 : term431 = True.
Proof. exact (TRANS (@lem5314967) (@lem5314971)). Qed.
Lemma lem5314973 : True = term431.
Proof. exact (SYM (@lem5314972)). Qed.
Lemma lem5314974 : term431.
Proof. exact (EQ_MP (@lem5314973) (@lem0)). Qed.
Lemma lem5314975 : term568.
Proof. exact (@lem5314964 (@lem5314974)). Qed.
Lemma lem5314977 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314978 : term431 = term432.
Proof. exact (@lem5314977 (NUMERAL 0) term386). Qed.
Lemma lem5314979 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5314980 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5314981 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5314980 h1) (fun h1 : term432 = True => @lem5314979)). Qed.
Lemma lem5314982 : term432 = True.
Proof. exact (EQ_MP (@lem5314981) (@lem5314979)). Qed.
Lemma lem5314983 : term431 = True.
Proof. exact (TRANS (@lem5314978) (@lem5314982)). Qed.
Lemma lem5314984 : True = term431.
Proof. exact (SYM (@lem5314983)). Qed.
Lemma lem5314985 : term431.
Proof. exact (EQ_MP (@lem5314984) (@lem0)). Qed.
Lemma lem5314986 : term566 = term569.
Proof. exact (@lem5314975 (@lem5314985)). Qed.
Lemma lem5314988 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314989 : term471 = term358.
Proof. exact (@lem5314988 term386). Qed.
Lemma lem5314991 (x : nat) : (term470 x) = term358.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5314992 : term471 = term358.
Proof. exact (@lem5314991 term386). Qed.
Lemma lem5314993 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5314994 : term472 = term463.
Proof. exact (MK_COMB (@lem5314993) (@lem5314992)). Qed.
Lemma lem5314995 : term569 = term565.
Proof. exact (MK_COMB (@lem5314994) (@lem5314989)). Qed.
Lemma lem5314997 (m : nat) (n : nat) : (term426 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5314998 : term565 = term570.
Proof. exact (@lem5314997 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5314999 : term570 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5315000 : term565 = False.
Proof. exact (TRANS (@lem5314998) (@lem5314999)). Qed.
Lemma lem5315001 : term569 = False.
Proof. exact (TRANS (@lem5314995) (@lem5315000)). Qed.
Lemma lem5315002 : term566 = False.
Proof. exact (TRANS (@lem5314986) (@lem5315001)). Qed.
Lemma lem5315003 : term565 = False.
Proof. exact (TRANS (@lem5314963) (@lem5315002)). Qed.
Lemma lem5315004 : term564 = False.
Proof. exact (TRANS (@lem5314954) (@lem5315003)). Qed.
Lemma lem5315005 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : False.
Proof. exact (EQ_MP (@lem5315004) (@lem5314951 s c l x0 h1)). Qed.
Lemma lem5315007 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : term624 s c l x0.
Proof. exact (h1). Qed.
Lemma lem5315008 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : (term624 s c l x0) = False.
Proof. exact (prop_ext (fun h2 : term624 s c l x0 => @lem5315005 s c l x0 h1) (fun h2 : False => @lem5315007 s c l x0 h1)). Qed.
Lemma lem5315009 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term624 s c l x0) : False.
Proof. exact (EQ_MP (@lem5315008 s c l x0 h1) (@lem5315007 s c l x0 h1)). Qed.
Lemma lem5315010 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term589 s x0 l c) : term589 s x0 l c.
Proof. exact (h1). Qed.
Lemma lem5315011 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term589 s x0 l c) : term624 s c l x0.
Proof. exact (EQ_MP (@lem5314122 s c l x0) (@lem5315010 s x0 l c h1)). Qed.
Lemma lem5315012 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term589 s x0 l c) : (term624 s c l x0) = False.
Proof. exact (prop_ext (fun h2 : term624 s c l x0 => @lem5315009 s c l x0 h2) (fun h2 : False => @lem5315011 s x0 l c h1)). Qed.
Lemma lem5315013 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term589 s x0 l c) : False.
Proof. exact (EQ_MP (@lem5315012 s x0 l c h1) (@lem5315011 s x0 l c h1)). Qed.
Lemma lem5315014 (s : real -> Prop) (x0 : real) (l : real) (c : real) : term701 s x0 l c.
Proof. exact (fun h0 : term589 s x0 l c => @lem5315013 s x0 l c h0). Qed.
Lemma lem5315015 (s : real -> Prop) (x0 : real) (l : real) (c : real) : term702 s x0 l c.
Proof. exact (@lem1386578 (term587 s x0 l c)). Qed.
Lemma lem5315018 (s : real -> Prop) (x0 : real) (l : real) (c : real) : term587 s x0 l c.
Proof. exact (@lem5315015 s x0 l c (@lem5315014 s x0 l c)). Qed.
Lemma lem5315019 (x0 : real) (l : real) (c : real) (s : real -> Prop) (h1 : term22 s) : term584 s x0 l c.
Proof. exact (@lem5315018 s x0 l c (@lem5312995 s h1)). Qed.
Lemma lem5315020 (x0 : real) (s : real -> Prop) (l : real) (c : real) (h1 : term22 s) (h2 : real_lt l c) : term582 s x0 l c.
Proof. exact (@lem5315019 x0 l c s h1 (@lem5313048 l c h2)). Qed.
Lemma lem5315021 (x0 : real) (s : real -> Prop) (l : real) (c : real) (h1 : term22 s) (h2 : @IN real x0 s) (h3 : real_lt l c) : term579 x0 l c.
Proof. exact (@lem5315020 x0 s l c h1 h3 (@lem5313897 x0 s h2)). Qed.
Lemma lem5315022 (x0 : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt l c) : term576 x0 l c.
Proof. exact (@lem5315021 x0 s l c h2 h3 h4 (@lem5313904 c x0 s h1 h3)). Qed.
Lemma lem5315023 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term574 s x0 l c) : term575 x0 l c.
Proof. exact (proj2 (@lem5313895 s x0 l c h1)). Qed.
Lemma lem5315024 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term574 s x0 l c) : @IN real x0 s.
Proof. exact (proj1 (@lem5313895 s x0 l c h1)). Qed.
Lemma lem5315025 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt l c) (h5 : term575 x0 l c) : False.
Proof. exact (@lem5315022 x0 s l c h1 h2 h3 h4 (@lem5313896 x0 l c h5)). Qed.
Lemma lem5315026 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt l c) (h5 : term575 x0 l c) : (@IN real x0 s) = False.
Proof. exact (prop_ext (fun h6 : @IN real x0 s => @lem5315025 s x0 l c h1 h2 h3 h4 h5) (fun h6 : False => @lem5313897 x0 s h3)). Qed.
Lemma lem5315027 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt l c) (h5 : term575 x0 l c) : False.
Proof. exact (EQ_MP (@lem5315026 s x0 l c h1 h2 h3 h4 h5) (@lem5313897 x0 s h3)). Qed.
Lemma lem5315028 (x0 : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term574 s x0 l c) (h4 : @IN real x0 s) (h5 : real_lt l c) : (term575 x0 l c) = False.
Proof. exact (prop_ext (fun h6 : term575 x0 l c => @lem5315027 s x0 l c h1 h2 h4 h5 h6) (fun h6 : False => @lem5315023 s x0 l c h3)). Qed.
Lemma lem5315029 (x0 : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term574 s x0 l c) (h4 : @IN real x0 s) (h5 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5315028 x0 s l c h1 h2 h3 h4 h5) (@lem5315023 s x0 l c h3)). Qed.
Lemma lem5315030 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term574 s x0 l c) (h4 : real_lt l c) : (@IN real x0 s) = False.
Proof. exact (prop_ext (fun h5 : @IN real x0 s => @lem5315029 x0 s l c h1 h2 h3 h5 h4) (fun h5 : False => @lem5315024 s x0 l c h3)). Qed.
Lemma lem5315031 (s : real -> Prop) (x0 : real) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term574 s x0 l c) (h4 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5315030 s x0 l c h1 h2 h3 h4) (@lem5315024 s x0 l c h3)). Qed.
Lemma lem5315032 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term346 s l c) (h3 : term22 s) (h4 : real_lt l c) : False.
Proof. exact (ex_elim (@lem5313894 s l c h2) (fun x0 : real => fun h0 : term703 s l c x0 => @lem5315031 s x0 l c h1 h3 h0 h4)). Qed.
Lemma lem5315033 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : real_lt l c) : term704 s l c.
Proof. exact (fun h0 : term346 s l c => @lem5315032 s l c h1 h0 h2 h3). Qed.
Lemma lem5315034 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : real_lt l c) : term705 s l c.
Proof. exact (conj (@lem5313893 s l c h2 h3) (@lem5315033 s l c h1 h2 h3)). Qed.
Lemma lem5315035 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term22 s) (h3 : real_lt l c) : term706 s l c.
Proof. exact (@lem5313054 s l c (@lem5315034 s l c h1 h2 h3)). Qed.
Lemma lem5315036 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) (h4 : real_lt l c) : False.
Proof. exact (@lem5315035 s l c h1 h3 h4 (@lem5313051 c l s h2)). Qed.
Lemma lem5315037 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) (h4 : real_lt l c) : (real_lt l c) = False.
Proof. exact (prop_ext (fun h5 : real_lt l c => @lem5315036 s l c h1 h2 h3 h4) (fun h5 : False => @lem5313048 l c h4)). Qed.
Lemma lem5315038 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) (h4 : real_lt l c) : False.
Proof. exact (EQ_MP (@lem5315037 s l c h1 h2 h3 h4) (@lem5313048 l c h4)). Qed.
Lemma lem5315039 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : term707 l c.
Proof. exact (fun h0 : real_lt l c => @lem5315038 s l c h1 h2 h3 h0). Qed.
Lemma lem5315040 (l : real) (c : real) : (term707 l c) = (term0 l c).
Proof. exact (@lem69 (real_lt l c)). Qed.
Lemma lem5315041 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : term0 l c.
Proof. exact (EQ_MP (@lem5315040 l c) (@lem5315039 c l s h1 h2 h3)). Qed.
Lemma lem5315042 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : real_le c l.
Proof. exact (EQ_MP (@lem5313047 c l) (@lem5315041 c l s h1 h2 h3)). Qed.
Lemma lem5315043 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : (term25 s c) = (real_le c l).
Proof. exact (prop_ext (fun h4 : term25 s c => @lem5315042 c l s h1 h2 h3) (fun h4 : real_le c l => @lem5313043 s c h1)). Qed.
Lemma lem5315044 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : real_le c l.
Proof. exact (EQ_MP (@lem5315043 c l s h1 h2 h3) (@lem5313043 s c h1)). Qed.
Lemma lem5315045 (c : real) (l : real) (s : real -> Prop) (h1 : term118 l s) (h2 : term22 s) : term708 s c l.
Proof. exact (fun h0 : term25 s c => @lem5315044 c l s h0 h1 h2). Qed.
Lemma lem5315046 (c : real) (l : real) (h1 : real_le c l) : real_le c l.
Proof. exact (h1). Qed.
Lemma lem5315049 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5315050 (h1 : term709) : term709.
Proof. exact (h1). Qed.
Lemma lem5315051 (x : real) (h1 : term709) : term710 x.
Proof. exact (@lem5315050 h1 x). Qed.
Lemma lem5315052 (x : real) : (term710 x) = (term711 x).
Proof. exact (eq_refl (term710 x)). Qed.
Lemma lem5315053 (x : real) (h1 : term709) : term711 x.
Proof. exact (EQ_MP (@lem5315052 x) (@lem5315051 x h1)). Qed.
Lemma lem5315054 (x : real) (y : real) (h1 : term709) : term712 x y.
Proof. exact (@lem5315053 x h1 y). Qed.
Lemma lem5315055 (y : real) (x : real) : (term712 x y) = (term713 y x).
Proof. exact (eq_refl (term712 x y)). Qed.
Lemma lem5315056 (y : real) (x : real) (h1 : term709) : term713 y x.
Proof. exact (EQ_MP (@lem5315055 y x) (@lem5315054 x y h1)). Qed.
Lemma lem5315057 (y : real) (x : real) (z : real) (h1 : term709) : term714 y x z.
Proof. exact (@lem5315056 y x h1 z). Qed.
Lemma lem5315058 (y : real) (x : real) (z : real) : (term714 y x z) = (term715 y x z).
Proof. exact (eq_refl (term714 y x z)). Qed.
Lemma lem5315059 (y : real) (x : real) (z : real) (h1 : term709) : term715 y x z.
Proof. exact (EQ_MP (@lem5315058 y x z) (@lem5315057 y x z h1)). Qed.
Lemma lem5315060 (x : real) (y : real) (z : real) (h1 : term716 x y z) : term716 x y z.
Proof. exact (h1). Qed.
Lemma lem5315061 (x : real) (y : real) (z : real) (h1 : term709) (h2 : term716 x y z) : real_le x z.
Proof. exact (@lem5315059 y x z h1 (@lem5315060 x y z h2)). Qed.
Lemma lem5315062 (x : real) (y : real) (z : real) (h1 : term716 x y z) : term717 x z.
Proof. exact (fun h0 : term709 => @lem5315061 x y z h0 h1). Qed.
Lemma lem5315063 (x : real) (z : real) (h1 : term718 x z) : term718 x z.
Proof. exact (h1). Qed.
Lemma lem5315064 (x : real) (z : real) (h1 : term718 x z) : term717 x z.
Proof. exact (ex_elim (@lem5315063 x z h1) (fun y : real => fun h0 : term719 x z y => @lem5315062 x y z h0)). Qed.
Lemma lem5315065 (h1 : term709) : term709.
Proof. exact (h1). Qed.
Lemma lem5315066 (x : real) (z : real) (h1 : term709) (h2 : term718 x z) : real_le x z.
Proof. exact (@lem5315064 x z h2 (@lem5315065 h1)). Qed.
Lemma lem5315067 (x : real) (z : real) (h1 : term709) : term720 x z.
Proof. exact (fun h0 : term718 x z => @lem5315066 x z h1 h0). Qed.
Lemma lem5315068 (x : real) (h1 : term709) : term721 x.
Proof. exact (fun z : real => @lem5315067 x z h1). Qed.
Lemma lem5315069 (h1 : term709) : term722.
Proof. exact (fun x : real => @lem5315068 x h1). Qed.
Lemma lem5315070 : term723.
Proof. exact (fun h0 : term709 => @lem5315069 h0). Qed.
Lemma lem5315071 : term722.
Proof. exact (@lem5315070 (@lem1339577)). Qed.
Lemma lem5315072 (x : real) : term724 x.
Proof. exact (@lem5315071 x). Qed.
Lemma lem5315073 (x : real) : (term724 x) = (term721 x).
Proof. exact (eq_refl (term724 x)). Qed.
Lemma lem5315074 (x : real) : term721 x.
Proof. exact (EQ_MP (@lem5315073 x) (@lem5315072 x)). Qed.
Lemma lem5315075 (x : real) (z : real) : term725 x z.
Proof. exact (@lem5315074 x z). Qed.
Lemma lem5315076 (x : real) (z : real) : (term725 x z) = (term720 x z).
Proof. exact (eq_refl (term725 x z)). Qed.
Lemma lem5315079 (x : real) (z : real) : term720 x z.
Proof. exact (EQ_MP (@lem5315076 x z) (@lem5315075 x z)). Qed.
Lemma lem5315080 (c : real) (x : real) : term720 c x.
Proof. exact (@lem5315079 c x). Qed.
Lemma lem5315094 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term61 s l x.
Proof. exact (@lem5312997 s l h1 x). Qed.
Lemma lem5315095 (s : real -> Prop) (l : real) (x : real) : (term61 s l x) = (term54 s l x).
Proof. exact (eq_refl (term61 s l x)). Qed.
Lemma lem5315096 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term54 s l x.
Proof. exact (EQ_MP (@lem5315095 s l x) (@lem5315094 x s l h1)). Qed.
Lemma lem5315097 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5315098 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : real_le l x.
Proof. exact (@lem5315096 x s l h1 (@lem5315097 x s h2)). Qed.
Lemma lem5315099 (l : real) (x : real) : (real_le l x) = ((real_le l x) = True).
Proof. exact (@lem7 (real_le l x)). Qed.
Lemma lem5315100 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le l x) = True.
Proof. exact (EQ_MP (@lem5315099 l x) (@lem5315098 l x s h1 h2)). Qed.
Lemma lem5315118 (c : real) (l : real) : (real_le c l) = ((real_le c l) = True).
Proof. exact (@lem7 (real_le c l)). Qed.
Lemma lem5315120 (x : real) (s : real -> Prop) : (@IN real x s) = ((@IN real x s) = True).
Proof. exact (@lem7 (@IN real x s)). Qed.
Lemma lem5315125 (c : real) (l : real) (h1 : real_le c l) : (real_le c l) = True.
Proof. exact (EQ_MP (@lem5315118 c l) (@lem5315046 c l h1)). Qed.
Lemma lem5315126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5315127 (c : real) (l : real) (h1 : real_le c l) : (term592 c l) = (and True).
Proof. exact (MK_COMB (@lem5315126) (@lem5315125 c l h1)). Qed.
Lemma lem5315129 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term726 s l x.
Proof. exact (fun h0 : @IN real x s => @lem5315100 l x s h1 h0). Qed.
Lemma lem5315131 (x : real) (s : real -> Prop) (h1 : @IN real x s) : (@IN real x s) = True.
Proof. exact (EQ_MP (@lem5315120 x s) (@lem5315049 x s h1)). Qed.
Lemma lem5315132 (x : real) (s : real -> Prop) (h1 : @IN real x s) : True = (@IN real x s).
Proof. exact (SYM (@lem5315131 x s h1)). Qed.
Lemma lem5315133 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (EQ_MP (@lem5315132 x s h1) (@lem0)). Qed.
Lemma lem5315134 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le l x) = True.
Proof. exact (@lem5315129 x s l h1 (@lem5315133 x s h2)). Qed.
Lemma lem5315135 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : (term716 c l x) = (True /\ True).
Proof. exact (MK_COMB (@lem5315127 c l h3) (@lem5315134 l x s h1 h2)). Qed.
Lemma lem5315137 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5315138 : (True /\ True) = True.
Proof. exact (@lem5315137 True). Qed.
Lemma lem5315139 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : (term716 c l x) = True.
Proof. exact (TRANS (@lem5315135 x s c l h1 h2 h3) (@lem5315138)). Qed.
Lemma lem5315140 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : True = (term716 c l x).
Proof. exact (SYM (@lem5315139 x s c l h1 h2 h3)). Qed.
Lemma lem5315141 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : term716 c l x.
Proof. exact (EQ_MP (@lem5315140 x s c l h1 h2 h3) (@lem0)). Qed.
Lemma lem5315142 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : term718 c x.
Proof. exact (ex_intro (term719 c x) l (@lem5315141 x s c l h1 h2 h3)). Qed.
Lemma lem5315143 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : real_le c x.
Proof. exact (@lem5315080 c x (@lem5315142 x s c l h1 h2 h3)). Qed.
Lemma lem5315144 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : (@IN real x s) = (real_le c x).
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5315143 x s c l h1 h2 h3) (fun h4 : real_le c x => @lem5315049 x s h2)). Qed.
Lemma lem5315145 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : real_le c x.
Proof. exact (EQ_MP (@lem5315144 x s c l h1 h2 h3) (@lem5315049 x s h2)). Qed.
Lemma lem5315146 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : term54 s c x.
Proof. exact (fun h0 : @IN real x s => @lem5315145 x s c l h1 h0 h2). Qed.
Lemma lem5315152 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : term25 s c.
Proof. exact (fun x : real => @lem5315146 x s c l h1 h2). Qed.
Lemma lem5315153 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : (real_le c l) = (term25 s c).
Proof. exact (prop_ext (fun h3 : real_le c l => @lem5315152 s c l h1 h2) (fun h3 : term25 s c => @lem5315046 c l h2)). Qed.
Lemma lem5315154 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : term25 s c.
Proof. exact (EQ_MP (@lem5315153 s c l h1 h2) (@lem5315046 c l h2)). Qed.
Lemma lem5315155 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term727 l s c.
Proof. exact (fun h0 : real_le c l => @lem5315154 s c l h1 h0). Qed.
Lemma lem5315156 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : term728 l s c.
Proof. exact (conj (@lem5315045 c l s h2 h3) (@lem5315155 c s l h1)). Qed.
Lemma lem5315157 (s : real -> Prop) (c : real) (l : real) : (term728 l s c) = ((term25 s c) = (real_le c l)).
Proof. exact (@lem32 (term25 s c) (real_le c l)). Qed.
Lemma lem5315158 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5315157 s c l) (@lem5315156 c l s h1 h2 h3)). Qed.
Lemma lem5315163 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : term339 s l.
Proof. exact (fun c : real => @lem5315158 c l s h1 h2 h3). Qed.
Lemma lem5315164 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : has_inf s l.
Proof. exact (EQ_MP (@lem5313042 s l) (@lem5315163 l s h1 h2 h3)). Qed.
Lemma lem5315165 (l : real) (s : real -> Prop) (h1 : term334 l s) : term333 l s.
Proof. exact (proj2 (@lem5312993 l s h1)). Qed.
Lemma lem5315166 (l : real) (s : real -> Prop) (h1 : term334 l s) : term22 s.
Proof. exact (proj1 (@lem5312993 l s h1)). Qed.
Lemma lem5315167 (l : real) (s : real -> Prop) (h1 : term333 l s) : term118 l s.
Proof. exact (proj2 (@lem5312994 l s h1)). Qed.
Lemma lem5315168 (l : real) (s : real -> Prop) (h1 : term333 l s) : term25 s l.
Proof. exact (proj1 (@lem5312994 l s h1)). Qed.
Lemma lem5315169 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : (term118 l s) = (has_inf s l).
Proof. exact (prop_ext (fun h4 : term118 l s => @lem5315164 l s h1 h2 h3) (fun h4 : has_inf s l => @lem5312996 l s h2)). Qed.
Lemma lem5315170 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315169 l s h1 h2 h3) (@lem5312996 l s h2)). Qed.
Lemma lem5315171 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : (term25 s l) = (has_inf s l).
Proof. exact (prop_ext (fun h4 : term25 s l => @lem5315170 l s h1 h2 h3) (fun h4 : has_inf s l => @lem5312997 s l h1)). Qed.
Lemma lem5315172 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315171 l s h1 h2 h3) (@lem5312997 s l h1)). Qed.
Lemma lem5315173 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term22 s) (h3 : term333 l s) : (term118 l s) = (has_inf s l).
Proof. exact (prop_ext (fun h4 : term118 l s => @lem5315172 l s h1 h4 h2) (fun h4 : has_inf s l => @lem5315167 l s h3)). Qed.
Lemma lem5315174 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term22 s) (h3 : term333 l s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315173 l s h1 h2 h3) (@lem5315167 l s h3)). Qed.
Lemma lem5315175 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : (term25 s l) = (has_inf s l).
Proof. exact (prop_ext (fun h3 : term25 s l => @lem5315174 l s h3 h1 h2) (fun h3 : has_inf s l => @lem5315168 l s h2)). Qed.
Lemma lem5315176 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315175 l s h1 h2) (@lem5315168 l s h2)). Qed.
Lemma lem5315177 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : (term22 s) = (has_inf s l).
Proof. exact (prop_ext (fun h3 : term22 s => @lem5315176 l s h1 h2) (fun h3 : has_inf s l => @lem5312995 s h1)). Qed.
Lemma lem5315178 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315177 l s h1 h2) (@lem5312995 s h1)). Qed.
Lemma lem5315179 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term334 l s) : (term333 l s) = (has_inf s l).
Proof. exact (prop_ext (fun h3 : term333 l s => @lem5315178 l s h1 h3) (fun h3 : has_inf s l => @lem5315165 l s h2)). Qed.
Lemma lem5315180 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term334 l s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315179 l s h1 h2) (@lem5315165 l s h2)). Qed.
Lemma lem5315181 (l : real) (s : real -> Prop) (h1 : term334 l s) : (term22 s) = (has_inf s l).
Proof. exact (prop_ext (fun h2 : term22 s => @lem5315180 l s h2 h1) (fun h2 : has_inf s l => @lem5315166 l s h1)). Qed.
Lemma lem5315182 (l : real) (s : real -> Prop) (h1 : term334 l s) : has_inf s l.
Proof. exact (EQ_MP (@lem5315181 l s h1) (@lem5315166 l s h1)). Qed.
Lemma lem5315183 (s : real -> Prop) (l : real) : term729 s l.
Proof. exact (fun h0 : term334 l s => @lem5315182 l s h0). Qed.
Lemma lem5315184 (s : real -> Prop) (l : real) : term730 s l.
Proof. exact (conj (@lem5312992 l s) (@lem5315183 s l)). Qed.
Lemma lem5315185 (l : real) (s : real -> Prop) : (term730 s l) = ((has_inf s l) = (term334 l s)).
Proof. exact (@lem32 (has_inf s l) (term334 l s)). Qed.
Lemma lem5315186 (l : real) (s : real -> Prop) : (has_inf s l) = (term334 l s).
Proof. exact (EQ_MP (@lem5315185 l s) (@lem5315184 s l)). Qed.
Lemma lem5315191 (s : real -> Prop) : term731 s.
Proof. exact (fun l : real => @lem5315186 l s). Qed.
Lemma lem5315196 : term732.
Proof. exact (fun s : real -> Prop => @lem5315191 s). Qed.
