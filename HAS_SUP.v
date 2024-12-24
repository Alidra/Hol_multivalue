Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SUP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SUP_APPROACH_spec.
Require Import HAS_SUP_SUP_spec.
Require Import HAS_SUP_UBOUND_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_NOT_LT_spec.
Require Import has_sup_spec.
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
Require Import thm1367763_spec.
Require Import thm1367771_spec.
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
Require Import thm1982759_spec.
Require Import thm1982761_spec.
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
Lemma lem5315199 (y : real) (x : real) (h1 : (term0 x y) = (real_le y x)) : (term0 x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem5315200 (y : real) (x : real) (h1 : (term0 x y) = (real_le y x)) : (real_le y x) = (term0 x y).
Proof. exact (SYM (@lem5315199 y x h1)). Qed.
Lemma lem5315201 (x : real) (y : real) (h1 : (real_le y x) = (term0 x y)) : (real_le y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem5315202 (x : real) (y : real) (h1 : (real_le y x) = (term0 x y)) : (term0 x y) = (real_le y x).
Proof. exact (SYM (@lem5315201 x y h1)). Qed.
Lemma lem5315203 (x : real) (y : real) : ((term0 x y) = (real_le y x)) = ((real_le y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_le y x) => @lem5315200 y x h1) (fun h1 : (real_le y x) = (term0 x y) => @lem5315202 x y h1)). Qed.
Lemma lem5315204 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem5315203 x y)). Qed.
Lemma lem5315205 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315206 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem5315205) (@lem5315204 x)). Qed.
Lemma lem5315207 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem5315206 x)). Qed.
Lemma lem5315208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315209 : term7 = term8.
Proof. exact (MK_COMB (@lem5315208) (@lem5315207)). Qed.
Lemma lem5315210 : term8.
Proof. exact (EQ_MP (@lem5315209) (@lem1376537)). Qed.
Lemma lem5315211 (x : real) : term9 x.
Proof. exact (@lem5315210 x). Qed.
Lemma lem5315212 (x : real) : (term9 x) = (term4 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem5315213 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem5315212 x) (@lem5315211 x)). Qed.
Lemma lem5315214 (x : real) (y : real) : term10 x y.
Proof. exact (@lem5315213 x y). Qed.
Lemma lem5315215 (x : real) (y : real) : (term10 x y) = ((real_le y x) = (term0 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem5315217 (t1 : Prop) : term11 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5315218 (t1 : Prop) : (term11 t1) = (term12 t1).
Proof. exact (eq_refl (term11 t1)). Qed.
Lemma lem5315219 (t1 : Prop) : term12 t1.
Proof. exact (EQ_MP (@lem5315218 t1) (@lem5315217 t1)). Qed.
Lemma lem5315220 (t1 : Prop) (t2 : Prop) : term13 t1 t2.
Proof. exact (@lem5315219 t1 t2). Qed.
Lemma lem5315221 (t1 : Prop) (t2 : Prop) : (term13 t1 t2) = (term14 t1 t2).
Proof. exact (eq_refl (term13 t1 t2)). Qed.
Lemma lem5315222 (t1 : Prop) (t2 : Prop) : term14 t1 t2.
Proof. exact (EQ_MP (@lem5315221 t1 t2) (@lem5315220 t1 t2)). Qed.
Lemma lem5315223 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term15 t1 t2 t3.
Proof. exact (@lem5315222 t1 t2 t3). Qed.
Lemma lem5315224 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term15 t1 t2 t3) = ((term16 t1 t2 t3) = (term17 t1 t2 t3)).
Proof. exact (eq_refl (term15 t1 t2 t3)). Qed.
Lemma lem5315225 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (EQ_MP (@lem5315224 t1 t2 t3) (@lem5315223 t1 t2 t3)). Qed.
Lemma lem5315226 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (SYM (@lem5315225 t1 t2 t3)). Qed.
Lemma lem5315227 (t1 : Prop) : term11 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5315228 (t1 : Prop) : (term11 t1) = (term12 t1).
Proof. exact (eq_refl (term11 t1)). Qed.
Lemma lem5315229 (t1 : Prop) : term12 t1.
Proof. exact (EQ_MP (@lem5315228 t1) (@lem5315227 t1)). Qed.
Lemma lem5315230 (t1 : Prop) (t2 : Prop) : term13 t1 t2.
Proof. exact (@lem5315229 t1 t2). Qed.
Lemma lem5315231 (t1 : Prop) (t2 : Prop) : (term13 t1 t2) = (term14 t1 t2).
Proof. exact (eq_refl (term13 t1 t2)). Qed.
Lemma lem5315232 (t1 : Prop) (t2 : Prop) : term14 t1 t2.
Proof. exact (EQ_MP (@lem5315231 t1 t2) (@lem5315230 t1 t2)). Qed.
Lemma lem5315233 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term15 t1 t2 t3.
Proof. exact (@lem5315232 t1 t2 t3). Qed.
Lemma lem5315234 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term15 t1 t2 t3) = ((term16 t1 t2 t3) = (term17 t1 t2 t3)).
Proof. exact (eq_refl (term15 t1 t2 t3)). Qed.
Lemma lem5315235 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (EQ_MP (@lem5315234 t1 t2 t3) (@lem5315233 t1 t2 t3)). Qed.
Lemma lem5315236 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (SYM (@lem5315235 t1 t2 t3)). Qed.
Lemma lem5315237 (s : real -> Prop) : term18 s.
Proof. exact (@lem5297166 s). Qed.
Lemma lem5315238 (s : real -> Prop) : (term18 s) = (term19 s).
Proof. exact (eq_refl (term18 s)). Qed.
Lemma lem5315239 (s : real -> Prop) : term19 s.
Proof. exact (EQ_MP (@lem5315238 s) (@lem5315237 s)). Qed.
Lemma lem5315240 (s : real -> Prop) (l : real) : term20 s l.
Proof. exact (@lem5315239 s l). Qed.
Lemma lem5315241 (s : real -> Prop) (l : real) : (term20 s l) = ((has_sup s l) = (term21 s l)).
Proof. exact (eq_refl (term20 s l)). Qed.
Lemma lem5315243 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5315245 (s : real -> Prop) (l : real) : (has_sup s l) = (term21 s l).
Proof. exact (EQ_MP (@lem5315241 s l) (@lem5315240 s l)). Qed.
Lemma lem5315264 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term21 s l.
Proof. exact (EQ_MP (@lem5315245 s l) (@lem5315243 s l h1)). Qed.
Lemma lem5315270 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term22 s.
Proof. exact (proj1 (@lem5315264 s l h1)). Qed.
Lemma lem5315271 (s : real -> Prop) : term23 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5315285 (s : real -> Prop) (l : real) (h1 : has_sup s l) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5315271 s (@lem5315270 s l h1)). Qed.
Lemma lem5315286 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5315287 (s : real -> Prop) (l : real) (h1 : has_sup s l) : (term22 s) = (~ False).
Proof. exact (MK_COMB (@lem5315286) (@lem5315285 s l h1)). Qed.
Lemma lem5315289 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5315290 (s : real -> Prop) (l : real) (h1 : has_sup s l) : (term22 s) = True.
Proof. exact (TRANS (@lem5315287 s l h1) (@lem5315289)). Qed.
Lemma lem5315291 (s : real -> Prop) (l : real) (h1 : has_sup s l) : True = (term22 s).
Proof. exact (SYM (@lem5315290 s l h1)). Qed.
Lemma lem5315292 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term22 s.
Proof. exact (EQ_MP (@lem5315291 s l h1) (@lem0)). Qed.
Lemma lem5315294 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5315295 (s : real -> Prop) (l : real) : (term25 s l) = (term26 s l).
Proof. exact (@lem5315294 (term25 s l)). Qed.
Lemma lem5315296 (s : real -> Prop) (l : real) : (term26 s l) = (term25 s l).
Proof. exact (SYM (@lem5315295 s l)). Qed.
Lemma lem5315297 (s : real -> Prop) (l : real) (h1 : term27 s l) : term27 s l.
Proof. exact (h1). Qed.
Lemma lem5315300 (s : real -> Prop) (l : real) (h1 : term28 s l) : term28 s l.
Proof. exact (h1). Qed.
Lemma lem5315301 (s : real -> Prop) (l : real) : term29 s l.
Proof. exact (fun h0 : term28 s l => @lem5315300 s l h0). Qed.
Lemma lem5315302 (s : real -> Prop) (l : real) (h1 : term29 s l) : term29 s l.
Proof. exact (h1). Qed.
Lemma lem5315303 (s : real -> Prop) (l : real) (h1 : term28 s l) : term28 s l.
Proof. exact (h1). Qed.
Lemma lem5315304 (s : real -> Prop) (l : real) (h1 : term29 s l) (h2 : term28 s l) : term28 s l.
Proof. exact (@lem5315302 s l h1 (@lem5315303 s l h2)). Qed.
Lemma lem5315305 (s : real -> Prop) (l : real) (h1 : term28 s l) : term30 s l.
Proof. exact (fun h0 : term29 s l => @lem5315304 s l h0 h1). Qed.
Lemma lem5315306 (s : real -> Prop) (l : real) (h1 : term29 s l) : term29 s l.
Proof. exact (h1). Qed.
Lemma lem5315307 (s : real -> Prop) (l : real) (h1 : term29 s l) (h2 : term28 s l) : term28 s l.
Proof. exact (@lem5315305 s l h2 (@lem5315306 s l h1)). Qed.
Lemma lem5315308 (s : real -> Prop) (l : real) (h1 : term29 s l) : term29 s l.
Proof. exact (fun h0 : term28 s l => @lem5315307 s l h1 h0). Qed.
Lemma lem5315309 (s : real -> Prop) (l : real) : term31 s l.
Proof. exact (fun h0 : term29 s l => @lem5315308 s l h0). Qed.
Lemma lem5315312 (s : real -> Prop) (l : real) : term29 s l.
Proof. exact (@lem5315309 s l (@lem5315301 s l)). Qed.
Lemma lem5315332 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5315333 : term32 = term33.
Proof. exact (@lem5315332 term34). Qed.
Lemma lem5315350 (s : real -> Prop) (l : real) : (term35 s l) = (term35 s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5315351 (s : real -> Prop) (l : real) : (term36 s l) = (term37 s l).
Proof. exact (MK_COMB (@lem5315350 s l) (@lem5315333)). Qed.
Lemma lem5315354 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5315355 (s : real -> Prop) (l : real) : (term28 s l) = (term39 s l).
Proof. exact (MK_COMB (@lem5315354 s l) (@lem5315351 s l)). Qed.
Lemma lem5315358 (l : real) : (term40 l) = (term41 l).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5315355 s l)). Qed.
Lemma lem5315359 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5315360 (l : real) : (term42 l) = (term43 l).
Proof. exact (MK_COMB (@lem5315359) (@lem5315358 l)). Qed.
Lemma lem5315365 : term44 = term45.
Proof. exact (fun_ext (fun l : real => @lem5315360 l)). Qed.
Lemma lem5315366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315375 : term46 = term47.
Proof. exact (MK_COMB (@lem5315366) (@lem5315365)). Qed.
Lemma lem5315384 (s : real -> Prop) (x : real) (b : real) : (term48 s x b) = (term48 s x b).
Proof. exact (eq_refl (term48 s x b)). Qed.
Lemma lem5315385 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5315384 s x b)). Qed.
Lemma lem5315386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315387 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5315386) (@lem5315385 s b)). Qed.
Lemma lem5315388 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (fun_ext (fun b : real => @lem5315387 s b)). Qed.
Lemma lem5315389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315390 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem5315389) (@lem5315388 s)). Qed.
Lemma lem5315391 : term53 = term53.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5315390 s)). Qed.
Lemma lem5315392 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5315393 : term34 = term34.
Proof. exact (MK_COMB (@lem5315392) (@lem5315391)). Qed.
Lemma lem5315394 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5315395 : term33 = term33.
Proof. exact (MK_COMB (@lem5315394) (@lem5315393)). Qed.
Lemma lem5315400 (s : real -> Prop) (x : real) (l : real) : (term54 s x l) = (term54 s x l).
Proof. exact (eq_refl (term54 s x l)). Qed.
Lemma lem5315401 (s : real -> Prop) (l : real) : (term55 s l) = (term55 s l).
Proof. exact (fun_ext (fun x : real => @lem5315400 s x l)). Qed.
Lemma lem5315402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315403 (s : real -> Prop) (l : real) : (term25 s l) = (term25 s l).
Proof. exact (MK_COMB (@lem5315402) (@lem5315401 s l)). Qed.
Lemma lem5315404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5315405 (s : real -> Prop) (l : real) : (term27 s l) = (term27 s l).
Proof. exact (MK_COMB (@lem5315404) (@lem5315403 s l)). Qed.
Lemma lem5315406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5315407 (s : real -> Prop) (l : real) : (term35 s l) = (term35 s l).
Proof. exact (MK_COMB (@lem5315406) (@lem5315405 s l)). Qed.
Lemma lem5315408 (s : real -> Prop) (l : real) : (term37 s l) = (term37 s l).
Proof. exact (MK_COMB (@lem5315407 s l) (@lem5315395)). Qed.
Lemma lem5315411 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5315412 (s : real -> Prop) (l : real) : (term39 s l) = (term39 s l).
Proof. exact (MK_COMB (@lem5315411 s l) (@lem5315408 s l)). Qed.
Lemma lem5315413 (l : real) : (term41 l) = (term41 l).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5315412 s l)). Qed.
Lemma lem5315414 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5315415 (l : real) : (term43 l) = (term43 l).
Proof. exact (MK_COMB (@lem5315414) (@lem5315413 l)). Qed.
Lemma lem5315416 : term45 = term45.
Proof. exact (fun_ext (fun l : real => @lem5315415 l)). Qed.
Lemma lem5315417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315418 : term47 = term47.
Proof. exact (MK_COMB (@lem5315417) (@lem5315416)). Qed.
Lemma lem5315467 : term46 = term47.
Proof. exact (TRANS (@lem5315375) (@lem5315418)). Qed.
Lemma lem5315468 : term47 = term46.
Proof. exact (SYM (@lem5315467)). Qed.
Lemma lem5315470 (s : real -> Prop) (l : real) (h1 : term27 s l) : term27 s l.
Proof. exact (h1). Qed.
Lemma lem5315471 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem5315477 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5315484 (s : real -> Prop) (x : real) (l : real) : (term56 s x l) = (term57 s x l).
Proof. exact (@lem17362 (@IN real x s) (real_le x l)). Qed.
Lemma lem5315485 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5315486 (s : real -> Prop) (l : real) : (term27 s l) = (term60 s l).
Proof. exact (@lem5315485 (term55 s l)). Qed.
Lemma lem5315487 (s : real -> Prop) (x : real) (l : real) : (term61 s l x) = (term54 s x l).
Proof. exact (eq_refl (term61 s l x)). Qed.
Lemma lem5315488 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5315489 (s : real -> Prop) (x : real) (l : real) : (term62 s l x) = (term56 s x l).
Proof. exact (MK_COMB (@lem5315488) (@lem5315487 s x l)). Qed.
Lemma lem5315490 (s : real -> Prop) (x : real) (l : real) : (term62 s l x) = (term57 s x l).
Proof. exact (TRANS (@lem5315489 s x l) (@lem5315484 s x l)). Qed.
Lemma lem5315491 (s : real -> Prop) (l : real) : (term63 s l) = (term64 s l).
Proof. exact (fun_ext (fun x : real => @lem5315490 s x l)). Qed.
Lemma lem5315492 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5315493 (s : real -> Prop) (l : real) : (term60 s l) = (term65 s l).
Proof. exact (MK_COMB (@lem5315492) (@lem5315491 s l)). Qed.
Lemma lem5315546 (s : real -> Prop) (l : real) : (term27 s l) = (term65 s l).
Proof. exact (TRANS (@lem5315486 s l) (@lem5315493 s l)). Qed.
Lemma lem5315547 (s : real -> Prop) (l : real) (h1 : term27 s l) : term65 s l.
Proof. exact (EQ_MP (@lem5315546 s l) (@lem5315470 s l h1)). Qed.
Lemma lem5315554 (b : real) (x : real) (s : real -> Prop) : (term66 b x s) = (term67 b x s).
Proof. exact (@lem17045 (has_sup s b) (@IN real x s)). Qed.
Lemma lem5315555 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5315556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5315557 (b : real) (x : real) (s : real -> Prop) : (term68 b x s) = (term69 b x s).
Proof. exact (MK_COMB (@lem5315556) (@lem5315554 b x s)). Qed.
Lemma lem5315558 (s : real -> Prop) (x : real) (b : real) : (term70 s x b) = (term71 s x b).
Proof. exact (MK_COMB (@lem5315557 b x s) (@lem5315555 x b)). Qed.
Lemma lem5315559 (s : real -> Prop) (x : real) (b : real) : (term48 s x b) = (term70 s x b).
Proof. exact (@lem17265 (term72 b x s) (real_le x b)). Qed.
Lemma lem5315560 (s : real -> Prop) (x : real) (b : real) : (term48 s x b) = (term71 s x b).
Proof. exact (TRANS (@lem5315559 s x b) (@lem5315558 s x b)). Qed.
Lemma lem5315561 (s : real -> Prop) (b : real) : (term49 s b) = (term73 s b).
Proof. exact (fun_ext (fun x : real => @lem5315560 s x b)). Qed.
Lemma lem5315562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315563 (s : real -> Prop) (b : real) : (term50 s b) = (term74 s b).
Proof. exact (MK_COMB (@lem5315562) (@lem5315561 s b)). Qed.
Lemma lem5315564 (s : real -> Prop) : (term51 s) = (term75 s).
Proof. exact (fun_ext (fun b : real => @lem5315563 s b)). Qed.
Lemma lem5315565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315566 (s : real -> Prop) : (term52 s) = (term76 s).
Proof. exact (MK_COMB (@lem5315565) (@lem5315564 s)). Qed.
Lemma lem5315567 : term53 = term77.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5315566 s)). Qed.
Lemma lem5315568 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5315629 : term34 = term78.
Proof. exact (MK_COMB (@lem5315568) (@lem5315567)). Qed.
Lemma lem5315630 (h1 : term34) : term78.
Proof. exact (EQ_MP (@lem5315629) (@lem5315471 h1)). Qed.
Lemma lem5315637 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5315662 (s : real -> Prop) (x : real) (b : real) : (term71 s x b) = (term71 s x b).
Proof. exact (eq_refl (term71 s x b)). Qed.
Lemma lem5315663 (s : real -> Prop) (b : real) : (term73 s b) = (term73 s b).
Proof. exact (fun_ext (fun x : real => @lem5315662 s x b)). Qed.
Lemma lem5315664 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315665 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (MK_COMB (@lem5315664) (@lem5315663 s b)). Qed.
Lemma lem5315666 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (fun_ext (fun b : real => @lem5315665 s b)). Qed.
Lemma lem5315667 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315668 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5315667) (@lem5315666 s)). Qed.
Lemma lem5315669 : term77 = term77.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5315668 s)). Qed.
Lemma lem5315670 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5315671 : term78 = term78.
Proof. exact (MK_COMB (@lem5315670) (@lem5315669)). Qed.
Lemma lem5315672 (h1 : term34) : term78.
Proof. exact (EQ_MP (@lem5315671) (@lem5315630 h1)). Qed.
Lemma lem5315688 (s : real -> Prop) (x : real) (l : real) (h1 : term57 s x l) : term57 s x l.
Proof. exact (h1). Qed.
Lemma lem5315694 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5315708 (s : real -> Prop) (x : real) (b : real) : (term71 s x b) = (term71 s x b).
Proof. exact (eq_refl (term71 s x b)). Qed.
Lemma lem5315709 (s : real -> Prop) (b : real) : (term73 s b) = (term73 s b).
Proof. exact (fun_ext (fun x : real => @lem5315708 s x b)). Qed.
Lemma lem5315710 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315711 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (MK_COMB (@lem5315710) (@lem5315709 s b)). Qed.
Lemma lem5315712 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (fun_ext (fun b : real => @lem5315711 s b)). Qed.
Lemma lem5315713 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5315714 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5315713) (@lem5315712 s)). Qed.
Lemma lem5315715 : term77 = term77.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5315714 s)). Qed.
Lemma lem5315716 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5315718 : term78 = term78.
Proof. exact (MK_COMB (@lem5315716) (@lem5315715)). Qed.
Lemma lem5315719 (h1 : term34) : term78.
Proof. exact (EQ_MP (@lem5315718) (@lem5315672 h1)). Qed.
Lemma lem5315728 (_69681 : real -> Prop) (h1 : term34) : term79 _69681.
Proof. exact (@lem5315719 h1 _69681). Qed.
Lemma lem5315729 (_69681 : real -> Prop) : (term79 _69681) = (term76 _69681).
Proof. exact (eq_refl (term79 _69681)). Qed.
Lemma lem5315730 (_69681 : real -> Prop) (h1 : term34) : term76 _69681.
Proof. exact (EQ_MP (@lem5315729 _69681) (@lem5315728 _69681 h1)). Qed.
Lemma lem5315731 (_69681 : real -> Prop) (_69682 : real) (h1 : term34) : term80 _69681 _69682.
Proof. exact (@lem5315730 _69681 h1 _69682). Qed.
Lemma lem5315732 (_69681 : real -> Prop) (_69682 : real) : (term80 _69681 _69682) = (term74 _69681 _69682).
Proof. exact (eq_refl (term80 _69681 _69682)). Qed.
Lemma lem5315733 (_69681 : real -> Prop) (_69682 : real) (h1 : term34) : term74 _69681 _69682.
Proof. exact (EQ_MP (@lem5315732 _69681 _69682) (@lem5315731 _69681 _69682 h1)). Qed.
Lemma lem5315734 (_69681 : real -> Prop) (_69682 : real) (_69683 : real) (h1 : term34) : term81 _69681 _69682 _69683.
Proof. exact (@lem5315733 _69681 _69682 h1 _69683). Qed.
Lemma lem5315735 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) : (term81 _69681 _69682 _69683) = (term71 _69681 _69683 _69682).
Proof. exact (eq_refl (term81 _69681 _69682 _69683)). Qed.
Lemma lem5315736 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) (h1 : term34) : term71 _69681 _69683 _69682.
Proof. exact (EQ_MP (@lem5315735 _69681 _69683 _69682) (@lem5315734 _69681 _69682 _69683 h1)). Qed.
Lemma lem5315738 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5315749 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) : (term71 _69681 _69683 _69682) = (term82 _69681 _69683 _69682).
Proof. exact (@lem5315236 (term83 _69681 _69682) (term84 _69683 _69681) (real_le _69683 _69682)). Qed.
Lemma lem5315750 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) (h1 : term34) : term82 _69681 _69683 _69682.
Proof. exact (EQ_MP (@lem5315749 _69681 _69683 _69682) (@lem5315736 _69681 _69683 _69682 h1)). Qed.
Lemma lem5315754 (s : real -> Prop) (x : real) (l : real) (h1 : term57 s x l) : term85 x l.
Proof. exact (proj2 (@lem5315688 s x l h1)). Qed.
Lemma lem5315756 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5315757 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term86 s l.
Proof. exact (fun h0 : term83 s l => @lem5315756 s l h1). Qed.
Lemma lem5315759 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5315760 (s : real -> Prop) (l : real) : (term86 s l) = (has_sup s l).
Proof. exact (@lem5315759 (has_sup s l)). Qed.
Lemma lem5315761 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (EQ_MP (@lem5315760 s l) (@lem5315757 s l h1)). Qed.
Lemma lem5315763 (s : real -> Prop) (x : real) (l : real) (h1 : term57 s x l) : @IN real x s.
Proof. exact (proj1 (@lem5315688 s x l h1)). Qed.
Lemma lem5315764 (s : real -> Prop) (x : real) (l : real) (h1 : term57 s x l) : term88 x s.
Proof. exact (fun h0 : term84 x s => @lem5315763 s x l h1). Qed.
Lemma lem5315766 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5315767 (x : real) (s : real -> Prop) : (term88 x s) = (@IN real x s).
Proof. exact (@lem5315766 (@IN real x s)). Qed.
Lemma lem5315768 (s : real -> Prop) (x : real) (l : real) (h1 : term57 s x l) : @IN real x s.
Proof. exact (EQ_MP (@lem5315767 x s) (@lem5315764 s x l h1)). Qed.
Lemma lem5315774 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5315775 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) : (term82 _69681 _69683 _69682) = (term89 _69681 _69683 _69682).
Proof. exact (@lem5315774 (term84 _69683 _69681) (term83 _69681 _69682) (real_le _69683 _69682)). Qed.
Lemma lem5315789 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5315790 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term90 _69681 _69683 _69682) = (term91 _69683 _69681 _69682).
Proof. exact (@lem5315789 (real_le _69683 _69682) (term83 _69681 _69682)). Qed.
Lemma lem5315796 (_69683 : real) (_69681 : real -> Prop) : (term92 _69683 _69681) = (term92 _69683 _69681).
Proof. exact (eq_refl (term92 _69683 _69681)). Qed.
Lemma lem5315797 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term89 _69681 _69683 _69682) = (term93 _69683 _69681 _69682).
Proof. exact (MK_COMB (@lem5315796 _69683 _69681) (@lem5315790 _69683 _69681 _69682)). Qed.
Lemma lem5315801 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5315802 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term93 _69683 _69681 _69682) = (term94 _69683 _69681 _69682).
Proof. exact (@lem5315801 (real_le _69683 _69682) (term84 _69683 _69681) (term83 _69681 _69682)). Qed.
Lemma lem5315818 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term89 _69681 _69683 _69682) = (term94 _69683 _69681 _69682).
Proof. exact (TRANS (@lem5315797 _69683 _69681 _69682) (@lem5315802 _69683 _69681 _69682)). Qed.
Lemma lem5315819 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term82 _69681 _69683 _69682) = (term94 _69683 _69681 _69682).
Proof. exact (TRANS (@lem5315775 _69681 _69683 _69682) (@lem5315818 _69683 _69681 _69682)). Qed.
Lemma lem5315820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5315821 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term95 _69681 _69683 _69682) = (term96 _69683 _69681 _69682).
Proof. exact (MK_COMB (@lem5315820) (@lem5315819 _69683 _69681 _69682)). Qed.
Lemma lem5315835 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5315836 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term67 _69682 _69683 _69681) = (term97 _69683 _69681 _69682).
Proof. exact (@lem5315835 (term84 _69683 _69681) (term83 _69681 _69682)). Qed.
Lemma lem5315842 (_69683 : real) (_69682 : real) : (term98 _69683 _69682) = (term98 _69683 _69682).
Proof. exact (eq_refl (term98 _69683 _69682)). Qed.
Lemma lem5315843 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : (term99 _69682 _69683 _69681) = (term94 _69683 _69681 _69682).
Proof. exact (MK_COMB (@lem5315842 _69683 _69682) (@lem5315836 _69683 _69681 _69682)). Qed.
Lemma lem5315854 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : ((term82 _69681 _69683 _69682) = (term99 _69682 _69683 _69681)) = ((term94 _69683 _69681 _69682) = (term94 _69683 _69681 _69682)).
Proof. exact (MK_COMB (@lem5315821 _69683 _69681 _69682) (@lem5315843 _69683 _69681 _69682)). Qed.
Lemma lem5315856 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5315857 (x : Prop) : (x = x) = True.
Proof. exact (@lem5315856 Prop x). Qed.
Lemma lem5315858 (_69683 : real) (_69681 : real -> Prop) (_69682 : real) : ((term94 _69683 _69681 _69682) = (term94 _69683 _69681 _69682)) = True.
Proof. exact (@lem5315857 (term94 _69683 _69681 _69682)). Qed.
Lemma lem5315859 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : ((term82 _69681 _69683 _69682) = (term99 _69682 _69683 _69681)) = True.
Proof. exact (TRANS (@lem5315854 _69683 _69681 _69682) (@lem5315858 _69683 _69681 _69682)). Qed.
Lemma lem5315860 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : True = ((term82 _69681 _69683 _69682) = (term99 _69682 _69683 _69681)).
Proof. exact (SYM (@lem5315859 _69682 _69683 _69681)). Qed.
Lemma lem5315861 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : (term82 _69681 _69683 _69682) = (term99 _69682 _69683 _69681).
Proof. exact (EQ_MP (@lem5315860 _69682 _69683 _69681) (@lem0)). Qed.
Lemma lem5315862 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) (h1 : term34) : term99 _69682 _69683 _69681.
Proof. exact (EQ_MP (@lem5315861 _69682 _69683 _69681) (@lem5315750 _69681 _69683 _69682 h1)). Qed.
Lemma lem5315864 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5315865 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) : (term99 _69682 _69683 _69681) = (term101 _69681 _69683 _69682).
Proof. exact (@lem5315864 (term67 _69682 _69683 _69681) (real_le _69683 _69682)). Qed.
Lemma lem5315867 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5315868 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : (term104 _69682 _69683 _69681) = (term105 _69682 _69683 _69681).
Proof. exact (@lem5315867 (term83 _69681 _69682) (term84 _69683 _69681)). Qed.
Lemma lem5315870 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5315871 (_69681 : real -> Prop) (_69682 : real) : (term107 _69681 _69682) = (has_sup _69681 _69682).
Proof. exact (@lem5315870 (has_sup _69681 _69682)). Qed.
Lemma lem5315872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5315873 (_69681 : real -> Prop) (_69682 : real) : (term108 _69681 _69682) = (term109 _69681 _69682).
Proof. exact (MK_COMB (@lem5315872) (@lem5315871 _69681 _69682)). Qed.
Lemma lem5315875 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5315876 (_69683 : real) (_69681 : real -> Prop) : (term110 _69683 _69681) = (@IN real _69683 _69681).
Proof. exact (@lem5315875 (@IN real _69683 _69681)). Qed.
Lemma lem5315877 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : (term105 _69682 _69683 _69681) = (term72 _69682 _69683 _69681).
Proof. exact (MK_COMB (@lem5315873 _69681 _69682) (@lem5315876 _69683 _69681)). Qed.
Lemma lem5315878 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : (term104 _69682 _69683 _69681) = (term72 _69682 _69683 _69681).
Proof. exact (TRANS (@lem5315868 _69682 _69683 _69681) (@lem5315877 _69682 _69683 _69681)). Qed.
Lemma lem5315879 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5315880 (_69682 : real) (_69683 : real) (_69681 : real -> Prop) : (term111 _69682 _69683 _69681) = (term112 _69682 _69683 _69681).
Proof. exact (MK_COMB (@lem5315879) (@lem5315878 _69682 _69683 _69681)). Qed.
Lemma lem5315881 (_69683 : real) (_69682 : real) : (real_le _69683 _69682) = (real_le _69683 _69682).
Proof. exact (eq_refl (real_le _69683 _69682)). Qed.
Lemma lem5315882 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) : (term101 _69681 _69683 _69682) = (term48 _69681 _69683 _69682).
Proof. exact (MK_COMB (@lem5315880 _69682 _69683 _69681) (@lem5315881 _69683 _69682)). Qed.
Lemma lem5315883 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) : (term99 _69682 _69683 _69681) = (term48 _69681 _69683 _69682).
Proof. exact (TRANS (@lem5315865 _69681 _69683 _69682) (@lem5315882 _69681 _69683 _69682)). Qed.
Lemma lem5315885 (x : real) (s : real -> Prop) (l : real) (h1 : term57 s x l) (h2 : has_sup s l) : term72 l x s.
Proof. exact (conj (@lem5315761 s l h2) (@lem5315768 s x l h1)). Qed.
Lemma lem5315887 (_69681 : real -> Prop) (_69683 : real) (_69682 : real) (h1 : term34) : term48 _69681 _69683 _69682.
Proof. exact (EQ_MP (@lem5315883 _69681 _69683 _69682) (@lem5315862 _69682 _69683 _69681 h1)). Qed.
Lemma lem5315888 (s : real -> Prop) (x : real) (l : real) (h1 : term34) : term48 s x l.
Proof. exact (@lem5315887 s x l h1). Qed.
Lemma lem5315891 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : real_le x l.
Proof. exact (@lem5315888 s x l h1 (@lem5315885 x s l h2 h3)). Qed.
Lemma lem5315892 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : term113 x l.
Proof. exact (fun h0 : term85 x l => @lem5315891 x s l h1 h2 h3). Qed.
Lemma lem5315894 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5315895 (x : real) (l : real) : (term113 x l) = (real_le x l).
Proof. exact (@lem5315894 (real_le x l)). Qed.
Lemma lem5315896 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : real_le x l.
Proof. exact (EQ_MP (@lem5315895 x l) (@lem5315892 x s l h1 h2 h3)). Qed.
Lemma lem5315899 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5315901 (x : real) (l : real) : (term85 x l) = (term114 x l).
Proof. exact (@lem5315899 (real_le x l)). Qed.
Lemma lem5315904 (s : real -> Prop) (x : real) (l : real) (h1 : term57 s x l) : term114 x l.
Proof. exact (EQ_MP (@lem5315901 x l) (@lem5315754 s x l h1)). Qed.
Lemma lem5315907 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (@lem5315904 s x l h2 (@lem5315896 x s l h1 h2 h3)). Qed.
Lemma lem5315908 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : term115.
Proof. exact (fun h0 : ~ False => @lem5315907 x s l h1 h2 h3). Qed.
Lemma lem5315910 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5315911 : term115 = False.
Proof. exact (@lem5315910 False). Qed.
Lemma lem5315912 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315911) (@lem5315908 x s l h1 h2 h3)). Qed.
Lemma lem5315913 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5315912 x s l h1 h2 h3) (fun h4 : False => @lem5315738 s l h3)). Qed.
Lemma lem5315914 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315913 x s l h1 h2 h3) (@lem5315738 s l h3)). Qed.
Lemma lem5315915 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5315914 x s l h1 h2 h3) (fun h4 : False => @lem5315694 s l h3)). Qed.
Lemma lem5315916 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315915 x s l h1 h2 h3) (@lem5315694 s l h3)). Qed.
Lemma lem5315917 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5315916 x s l h1 h2 h3) (fun h4 : False => @lem5315694 s l h3)). Qed.
Lemma lem5315918 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315917 x s l h1 h2 h3) (@lem5315694 s l h3)). Qed.
Lemma lem5315919 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : (term57 s x l) = False.
Proof. exact (prop_ext (fun h4 : term57 s x l => @lem5315918 x s l h1 h2 h3) (fun h4 : False => @lem5315688 s x l h2)). Qed.
Lemma lem5315920 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315919 x s l h1 h2 h3) (@lem5315688 s x l h2)). Qed.
Lemma lem5315921 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5315920 x s l h1 h2 h3) (fun h4 : False => @lem5315637 s l h3)). Qed.
Lemma lem5315922 (x : real) (s : real -> Prop) (l : real) (h1 : term34) (h2 : term57 s x l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315921 x s l h1 h2 h3) (@lem5315637 s l h3)). Qed.
Lemma lem5315923 (s : real -> Prop) (l : real) (h1 : term34) (h2 : term27 s l) (h3 : has_sup s l) : False.
Proof. exact (ex_elim (@lem5315547 s l h2) (fun x : real => fun h0 : term64 s l x => @lem5315922 x s l h1 h0 h3)). Qed.
Lemma lem5315924 (s : real -> Prop) (l : real) (h1 : term34) (h2 : term27 s l) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5315923 s l h1 h2 h3) (fun h4 : False => @lem5315477 s l h3)). Qed.
Lemma lem5315925 (s : real -> Prop) (l : real) (h1 : term34) (h2 : term27 s l) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315924 s l h1 h2 h3) (@lem5315477 s l h3)). Qed.
Lemma lem5315926 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_sup s l) : term32.
Proof. exact (fun h0 : term34 => @lem5315925 s l h0 h1 h2). Qed.
Lemma lem5315927 : term32 = term33.
Proof. exact (@lem69 term34). Qed.
Lemma lem5315928 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_sup s l) : term33.
Proof. exact (EQ_MP (@lem5315927) (@lem5315926 s l h1 h2)). Qed.
Lemma lem5315929 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term37 s l.
Proof. exact (fun h0 : term27 s l => @lem5315928 s l h0 h1). Qed.
Lemma lem5315930 (s : real -> Prop) (l : real) : term39 s l.
Proof. exact (fun h0 : has_sup s l => @lem5315929 s l h0). Qed.
Lemma lem5315935 (l : real) : term43 l.
Proof. exact (fun s : real -> Prop => @lem5315930 s l). Qed.
Lemma lem5315940 : term47.
Proof. exact (fun l : real => @lem5315935 l). Qed.
Lemma lem5315941 : term46.
Proof. exact (EQ_MP (@lem5315468) (@lem5315940)). Qed.
Lemma lem5315942 (l : real) : term116 l.
Proof. exact (@lem5315941 l). Qed.
Lemma lem5315943 (l : real) : (term116 l) = (term42 l).
Proof. exact (eq_refl (term116 l)). Qed.
Lemma lem5315944 (l : real) : term42 l.
Proof. exact (EQ_MP (@lem5315943 l) (@lem5315942 l)). Qed.
Lemma lem5315945 (l : real) (s : real -> Prop) : term117 l s.
Proof. exact (@lem5315944 l s). Qed.
Lemma lem5315946 (s : real -> Prop) (l : real) : (term117 l s) = (term28 s l).
Proof. exact (eq_refl (term117 l s)). Qed.
Lemma lem5315947 (s : real -> Prop) (l : real) : term28 s l.
Proof. exact (EQ_MP (@lem5315946 s l) (@lem5315945 l s)). Qed.
Lemma lem5315949 (s : real -> Prop) (l : real) : term28 s l.
Proof. exact (@lem5315312 s l (@lem5315947 s l)). Qed.
Lemma lem5315950 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term36 s l.
Proof. exact (@lem5315949 s l (@lem5315243 s l h1)). Qed.
Lemma lem5315951 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_sup s l) : term32.
Proof. exact (@lem5315950 s l h2 (@lem5315297 s l h1)). Qed.
Lemma lem5315952 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_sup s l) : False.
Proof. exact (@lem5315951 s l h1 h2 (@lem5293342)). Qed.
Lemma lem5315953 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_sup s l) : (term27 s l) = False.
Proof. exact (prop_ext (fun h3 : term27 s l => @lem5315952 s l h1 h2) (fun h3 : False => @lem5315297 s l h1)). Qed.
Lemma lem5315954 (s : real -> Prop) (l : real) (h1 : term27 s l) (h2 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5315953 s l h1 h2) (@lem5315297 s l h1)). Qed.
Lemma lem5315955 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term26 s l.
Proof. exact (fun h0 : term27 s l => @lem5315954 s l h0 h1). Qed.
Lemma lem5315956 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term25 s l.
Proof. exact (EQ_MP (@lem5315296 s l) (@lem5315955 s l h1)). Qed.
Lemma lem5315958 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5315959 (l : real) (s : real -> Prop) : (term118 l s) = (term119 l s).
Proof. exact (@lem5315958 (term118 l s)). Qed.
Lemma lem5315960 (l : real) (s : real -> Prop) : (term119 l s) = (term118 l s).
Proof. exact (SYM (@lem5315959 l s)). Qed.
Lemma lem5315961 (l : real) (s : real -> Prop) (h1 : term120 l s) : term120 l s.
Proof. exact (h1). Qed.
Lemma lem5315964 (l : real) (s : real -> Prop) (h1 : term121 l s) : term121 l s.
Proof. exact (h1). Qed.
Lemma lem5315965 (l : real) (s : real -> Prop) : term122 l s.
Proof. exact (fun h0 : term121 l s => @lem5315964 l s h0). Qed.
Lemma lem5315966 (l : real) (s : real -> Prop) (h1 : term122 l s) : term122 l s.
Proof. exact (h1). Qed.
Lemma lem5315967 (l : real) (s : real -> Prop) (h1 : term121 l s) : term121 l s.
Proof. exact (h1). Qed.
Lemma lem5315968 (l : real) (s : real -> Prop) (h1 : term122 l s) (h2 : term121 l s) : term121 l s.
Proof. exact (@lem5315966 l s h1 (@lem5315967 l s h2)). Qed.
Lemma lem5315969 (l : real) (s : real -> Prop) (h1 : term121 l s) : term123 l s.
Proof. exact (fun h0 : term122 l s => @lem5315968 l s h0 h1). Qed.
Lemma lem5315970 (l : real) (s : real -> Prop) (h1 : term122 l s) : term122 l s.
Proof. exact (h1). Qed.
Lemma lem5315971 (l : real) (s : real -> Prop) (h1 : term122 l s) (h2 : term121 l s) : term121 l s.
Proof. exact (@lem5315969 l s h2 (@lem5315970 l s h1)). Qed.
Lemma lem5315972 (l : real) (s : real -> Prop) (h1 : term122 l s) : term122 l s.
Proof. exact (fun h0 : term121 l s => @lem5315971 l s h1 h0). Qed.
Lemma lem5315973 (l : real) (s : real -> Prop) : term124 l s.
Proof. exact (fun h0 : term122 l s => @lem5315972 l s h0). Qed.
Lemma lem5315976 (l : real) (s : real -> Prop) : term122 l s.
Proof. exact (@lem5315973 l s (@lem5315965 l s)). Qed.
Lemma lem5316046 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5316047 : term125 = term126.
Proof. exact (@lem5316046 term127). Qed.
Lemma lem5316114 (l : real) (s : real -> Prop) : (term128 l s) = (term128 l s).
Proof. exact (eq_refl (term128 l s)). Qed.
Lemma lem5316115 (l : real) (s : real -> Prop) : (term129 l s) = (term130 l s).
Proof. exact (MK_COMB (@lem5316114 l s) (@lem5316047)). Qed.
Lemma lem5316118 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5316119 (l : real) (s : real -> Prop) : (term121 l s) = (term131 l s).
Proof. exact (MK_COMB (@lem5316118 s l) (@lem5316115 l s)). Qed.
Lemma lem5316122 (s : real -> Prop) : (term132 s) = (term133 s).
Proof. exact (fun_ext (fun l : real => @lem5316119 l s)). Qed.
Lemma lem5316123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316124 (s : real -> Prop) : (term134 s) = (term135 s).
Proof. exact (MK_COMB (@lem5316123) (@lem5316122 s)). Qed.
Lemma lem5316129 : term136 = term137.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316124 s)). Qed.
Lemma lem5316130 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316139 : term138 = term139.
Proof. exact (MK_COMB (@lem5316130) (@lem5316129)). Qed.
Lemma lem5316144 (s : real -> Prop) (c : real) (x : real) : (term140 s c x) = (term140 s c x).
Proof. exact (eq_refl (term140 s c x)). Qed.
Lemma lem5316145 (s : real -> Prop) (c : real) : (term141 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5316144 s c x)). Qed.
Lemma lem5316146 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316147 (s : real -> Prop) (c : real) : (term142 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5316146) (@lem5316145 s c)). Qed.
Lemma lem5316154 (s : real -> Prop) (c : real) (l : real) : (term143 s c l) = (term143 s c l).
Proof. exact (eq_refl (term143 s c l)). Qed.
Lemma lem5316155 (l : real) (s : real -> Prop) (c : real) : (term144 l s c) = (term144 l s c).
Proof. exact (MK_COMB (@lem5316154 s c l) (@lem5316147 s c)). Qed.
Lemma lem5316156 (l : real) (s : real -> Prop) : (term145 l s) = (term145 l s).
Proof. exact (fun_ext (fun c : real => @lem5316155 l s c)). Qed.
Lemma lem5316157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316158 (l : real) (s : real -> Prop) : (term146 l s) = (term146 l s).
Proof. exact (MK_COMB (@lem5316157) (@lem5316156 l s)). Qed.
Lemma lem5316159 (s : real -> Prop) : (term147 s) = (term147 s).
Proof. exact (fun_ext (fun l : real => @lem5316158 l s)). Qed.
Lemma lem5316160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316161 (s : real -> Prop) : (term148 s) = (term148 s).
Proof. exact (MK_COMB (@lem5316160) (@lem5316159 s)). Qed.
Lemma lem5316162 : term149 = term149.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316161 s)). Qed.
Lemma lem5316163 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316164 : term127 = term127.
Proof. exact (MK_COMB (@lem5316163) (@lem5316162)). Qed.
Lemma lem5316165 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5316166 : term126 = term126.
Proof. exact (MK_COMB (@lem5316165) (@lem5316164)). Qed.
Lemma lem5316171 (s : real -> Prop) (c : real) (x : real) : (term140 s c x) = (term140 s c x).
Proof. exact (eq_refl (term140 s c x)). Qed.
Lemma lem5316172 (s : real -> Prop) (c : real) : (term141 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5316171 s c x)). Qed.
Lemma lem5316173 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316174 (s : real -> Prop) (c : real) : (term142 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5316173) (@lem5316172 s c)). Qed.
Lemma lem5316177 (c : real) (l : real) : (term150 c l) = (term150 c l).
Proof. exact (eq_refl (term150 c l)). Qed.
Lemma lem5316178 (l : real) (s : real -> Prop) (c : real) : (term151 l s c) = (term151 l s c).
Proof. exact (MK_COMB (@lem5316177 c l) (@lem5316174 s c)). Qed.
Lemma lem5316179 (l : real) (s : real -> Prop) : (term152 l s) = (term152 l s).
Proof. exact (fun_ext (fun c : real => @lem5316178 l s c)). Qed.
Lemma lem5316180 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316181 (l : real) (s : real -> Prop) : (term118 l s) = (term118 l s).
Proof. exact (MK_COMB (@lem5316180) (@lem5316179 l s)). Qed.
Lemma lem5316182 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5316183 (l : real) (s : real -> Prop) : (term120 l s) = (term120 l s).
Proof. exact (MK_COMB (@lem5316182) (@lem5316181 l s)). Qed.
Lemma lem5316184 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5316185 (l : real) (s : real -> Prop) : (term128 l s) = (term128 l s).
Proof. exact (MK_COMB (@lem5316184) (@lem5316183 l s)). Qed.
Lemma lem5316186 (l : real) (s : real -> Prop) : (term130 l s) = (term130 l s).
Proof. exact (MK_COMB (@lem5316185 l s) (@lem5316166)). Qed.
Lemma lem5316189 (s : real -> Prop) (l : real) : (term38 s l) = (term38 s l).
Proof. exact (eq_refl (term38 s l)). Qed.
Lemma lem5316190 (l : real) (s : real -> Prop) : (term131 l s) = (term131 l s).
Proof. exact (MK_COMB (@lem5316189 s l) (@lem5316186 l s)). Qed.
Lemma lem5316191 (s : real -> Prop) : (term133 s) = (term133 s).
Proof. exact (fun_ext (fun l : real => @lem5316190 l s)). Qed.
Lemma lem5316192 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316193 (s : real -> Prop) : (term135 s) = (term135 s).
Proof. exact (MK_COMB (@lem5316192) (@lem5316191 s)). Qed.
Lemma lem5316194 : term137 = term137.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316193 s)). Qed.
Lemma lem5316195 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316196 : term139 = term139.
Proof. exact (MK_COMB (@lem5316195) (@lem5316194)). Qed.
Lemma lem5316261 : term138 = term139.
Proof. exact (TRANS (@lem5316139) (@lem5316196)). Qed.
Lemma lem5316262 : term139 = term138.
Proof. exact (SYM (@lem5316261)). Qed.
Lemma lem5316264 (l : real) (s : real -> Prop) (h1 : term120 l s) : term120 l s.
Proof. exact (h1). Qed.
Lemma lem5316265 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem5316271 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5316279 (s : real -> Prop) (c : real) (x : real) : (term153 s c x) = (term154 s c x).
Proof. exact (@lem17045 (@IN real x s) (real_lt c x)). Qed.
Lemma lem5316280 (P : real -> Prop) : (term155 P) = (term156 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5316281 (s : real -> Prop) (c : real) : (term157 s c) = (term158 s c).
Proof. exact (@lem5316280 (term141 s c)). Qed.
Lemma lem5316282 (s : real -> Prop) (c : real) (x : real) : (term159 s c x) = (term140 s c x).
Proof. exact (eq_refl (term159 s c x)). Qed.
Lemma lem5316283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5316284 (s : real -> Prop) (c : real) (x : real) : (term160 s c x) = (term153 s c x).
Proof. exact (MK_COMB (@lem5316283) (@lem5316282 s c x)). Qed.
Lemma lem5316285 (s : real -> Prop) (c : real) (x : real) : (term160 s c x) = (term154 s c x).
Proof. exact (TRANS (@lem5316284 s c x) (@lem5316279 s c x)). Qed.
Lemma lem5316286 (s : real -> Prop) (c : real) : (term161 s c) = (term162 s c).
Proof. exact (fun_ext (fun x : real => @lem5316285 s c x)). Qed.
Lemma lem5316287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316288 (s : real -> Prop) (c : real) : (term158 s c) = (term163 s c).
Proof. exact (MK_COMB (@lem5316287) (@lem5316286 s c)). Qed.
Lemma lem5316289 (s : real -> Prop) (c : real) : (term157 s c) = (term163 s c).
Proof. exact (TRANS (@lem5316281 s c) (@lem5316288 s c)). Qed.
Lemma lem5316291 (c : real) (l : real) : (term164 c l) = (term164 c l).
Proof. exact (eq_refl (term164 c l)). Qed.
Lemma lem5316292 (l : real) (s : real -> Prop) (c : real) : (term165 l s c) = (term166 l s c).
Proof. exact (MK_COMB (@lem5316291 c l) (@lem5316289 s c)). Qed.
Lemma lem5316293 (l : real) (s : real -> Prop) (c : real) : (term167 l s c) = (term165 l s c).
Proof. exact (@lem17362 (real_lt c l) (term142 s c)). Qed.
Lemma lem5316294 (l : real) (s : real -> Prop) (c : real) : (term167 l s c) = (term166 l s c).
Proof. exact (TRANS (@lem5316293 l s c) (@lem5316292 l s c)). Qed.
Lemma lem5316295 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5316296 (l : real) (s : real -> Prop) : (term120 l s) = (term168 l s).
Proof. exact (@lem5316295 (term152 l s)). Qed.
Lemma lem5316297 (l : real) (s : real -> Prop) (c : real) : (term169 l s c) = (term151 l s c).
Proof. exact (eq_refl (term169 l s c)). Qed.
Lemma lem5316298 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5316299 (l : real) (s : real -> Prop) (c : real) : (term170 l s c) = (term167 l s c).
Proof. exact (MK_COMB (@lem5316298) (@lem5316297 l s c)). Qed.
Lemma lem5316300 (l : real) (s : real -> Prop) (c : real) : (term170 l s c) = (term166 l s c).
Proof. exact (TRANS (@lem5316299 l s c) (@lem5316294 l s c)). Qed.
Lemma lem5316301 (l : real) (s : real -> Prop) : (term171 l s) = (term172 l s).
Proof. exact (fun_ext (fun c : real => @lem5316300 l s c)). Qed.
Lemma lem5316302 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316303 (l : real) (s : real -> Prop) : (term168 l s) = (term173 l s).
Proof. exact (MK_COMB (@lem5316302) (@lem5316301 l s)). Qed.
Lemma lem5316404 (l : real) (s : real -> Prop) : (term120 l s) = (term173 l s).
Proof. exact (TRANS (@lem5316296 l s) (@lem5316303 l s)). Qed.
Lemma lem5316405 (l : real) (s : real -> Prop) (h1 : term120 l s) : term173 l s.
Proof. exact (EQ_MP (@lem5316404 l s) (@lem5316264 l s h1)). Qed.
Lemma lem5316412 (s : real -> Prop) (c : real) (l : real) : (term174 s c l) = (term175 s c l).
Proof. exact (@lem17045 (has_sup s l) (real_lt c l)). Qed.
Lemma lem5316417 (s : real -> Prop) (c : real) (x : real) : (term140 s c x) = (term140 s c x).
Proof. exact (eq_refl (term140 s c x)). Qed.
Lemma lem5316418 (s : real -> Prop) (c : real) : (term141 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5316417 s c x)). Qed.
Lemma lem5316419 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316420 (s : real -> Prop) (c : real) : (term142 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5316419) (@lem5316418 s c)). Qed.
Lemma lem5316421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5316422 (s : real -> Prop) (c : real) (l : real) : (term176 s c l) = (term177 s c l).
Proof. exact (MK_COMB (@lem5316421) (@lem5316412 s c l)). Qed.
Lemma lem5316423 (l : real) (s : real -> Prop) (c : real) : (term178 l s c) = (term179 l s c).
Proof. exact (MK_COMB (@lem5316422 s c l) (@lem5316420 s c)). Qed.
Lemma lem5316424 (l : real) (s : real -> Prop) (c : real) : (term144 l s c) = (term178 l s c).
Proof. exact (@lem17265 (term180 s c l) (term142 s c)). Qed.
Lemma lem5316425 (l : real) (s : real -> Prop) (c : real) : (term144 l s c) = (term179 l s c).
Proof. exact (TRANS (@lem5316424 l s c) (@lem5316423 l s c)). Qed.
Lemma lem5316426 (l : real) (s : real -> Prop) : (term145 l s) = (term181 l s).
Proof. exact (fun_ext (fun c : real => @lem5316425 l s c)). Qed.
Lemma lem5316427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316428 (l : real) (s : real -> Prop) : (term146 l s) = (term182 l s).
Proof. exact (MK_COMB (@lem5316427) (@lem5316426 l s)). Qed.
Lemma lem5316429 (s : real -> Prop) : (term147 s) = (term183 s).
Proof. exact (fun_ext (fun l : real => @lem5316428 l s)). Qed.
Lemma lem5316430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316431 (s : real -> Prop) : (term148 s) = (term184 s).
Proof. exact (MK_COMB (@lem5316430) (@lem5316429 s)). Qed.
Lemma lem5316432 : term149 = term185.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316431 s)). Qed.
Lemma lem5316433 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316434 : term127 = term186.
Proof. exact (MK_COMB (@lem5316433) (@lem5316432)). Qed.
Lemma lem5316541 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5316542 (P : Prop) (Q : real -> Prop) : (term189 P Q) = (term190 P Q).
Proof. exact (@lem5316541 real P Q). Qed.
Lemma lem5316543 (l : real) (s : real -> Prop) (c : real) : (term191 l s c) = (term192 l s c).
Proof. exact (@lem5316542 (term175 s c l) (term141 s c)). Qed.
Lemma lem5316544 (s : real -> Prop) (c : real) (x : real) : (term159 s c x) = (term140 s c x).
Proof. exact (eq_refl (term159 s c x)). Qed.
Lemma lem5316545 (s : real -> Prop) (c : real) : (term193 s c) = (term141 s c).
Proof. exact (fun_ext (fun x : real => @lem5316544 s c x)). Qed.
Lemma lem5316546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316547 (s : real -> Prop) (c : real) : (term194 s c) = (term142 s c).
Proof. exact (MK_COMB (@lem5316546) (@lem5316545 s c)). Qed.
Lemma lem5316548 (s : real -> Prop) (c : real) (l : real) : (term177 s c l) = (term177 s c l).
Proof. exact (eq_refl (term177 s c l)). Qed.
Lemma lem5316549 (l : real) (s : real -> Prop) (c : real) : (term191 l s c) = (term179 l s c).
Proof. exact (MK_COMB (@lem5316548 s c l) (@lem5316547 s c)). Qed.
Lemma lem5316550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5316551 (l : real) (s : real -> Prop) (c : real) : (term195 l s c) = (term196 l s c).
Proof. exact (MK_COMB (@lem5316550) (@lem5316549 l s c)). Qed.
Lemma lem5316552 (s : real -> Prop) (c : real) (x : real) : (term159 s c x) = (term140 s c x).
Proof. exact (eq_refl (term159 s c x)). Qed.
Lemma lem5316553 (s : real -> Prop) (c : real) (l : real) : (term177 s c l) = (term177 s c l).
Proof. exact (eq_refl (term177 s c l)). Qed.
Lemma lem5316554 (l : real) (s : real -> Prop) (c : real) (x : real) : (term197 l s c x) = (term198 l s c x).
Proof. exact (MK_COMB (@lem5316553 s c l) (@lem5316552 s c x)). Qed.
Lemma lem5316555 (l : real) (s : real -> Prop) (c : real) : (term199 l s c) = (term200 l s c).
Proof. exact (fun_ext (fun x : real => @lem5316554 l s c x)). Qed.
Lemma lem5316556 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316557 (l : real) (s : real -> Prop) (c : real) : (term192 l s c) = (term201 l s c).
Proof. exact (MK_COMB (@lem5316556) (@lem5316555 l s c)). Qed.
Lemma lem5316558 (l : real) (s : real -> Prop) (c : real) : ((term191 l s c) = (term192 l s c)) = ((term179 l s c) = (term201 l s c)).
Proof. exact (MK_COMB (@lem5316551 l s c) (@lem5316557 l s c)). Qed.
Lemma lem5316559 (l : real) (s : real -> Prop) (c : real) : (term179 l s c) = (term201 l s c).
Proof. exact (EQ_MP (@lem5316558 l s c) (@lem5316543 l s c)). Qed.
Lemma lem5316560 (l : real) (s : real -> Prop) : (term181 l s) = (term202 l s).
Proof. exact (fun_ext (fun c : real => @lem5316559 l s c)). Qed.
Lemma lem5316561 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316562 (l : real) (s : real -> Prop) : (term182 l s) = (term203 l s).
Proof. exact (MK_COMB (@lem5316561) (@lem5316560 l s)). Qed.
Lemma lem5316564 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5316565 (P : type1626) : (term206 P) = (term207 P).
Proof. exact (@lem5316564 real real P). Qed.
Lemma lem5316566 (l : real) (s : real -> Prop) : (term208 l s) = (term209 l s).
Proof. exact (@lem5316565 (term210 l s)). Qed.
Lemma lem5316567 (l : real) (s : real -> Prop) (c : real) : (term211 l s c) = (term200 l s c).
Proof. exact (eq_refl (term211 l s c)). Qed.
Lemma lem5316568 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5316569 (l : real) (s : real -> Prop) (c : real) (x : real) : (term212 l s c x) = (term213 l s c x).
Proof. exact (MK_COMB (@lem5316567 l s c) (@lem5316568 x)). Qed.
Lemma lem5316570 (l : real) (s : real -> Prop) (c : real) (x : real) : (term213 l s c x) = (term198 l s c x).
Proof. exact (eq_refl (term213 l s c x)). Qed.
Lemma lem5316571 (l : real) (s : real -> Prop) (c : real) (x : real) : (term212 l s c x) = (term198 l s c x).
Proof. exact (TRANS (@lem5316569 l s c x) (@lem5316570 l s c x)). Qed.
Lemma lem5316572 (l : real) (s : real -> Prop) (c : real) : (term214 l s c) = (term200 l s c).
Proof. exact (fun_ext (fun x : real => @lem5316571 l s c x)). Qed.
Lemma lem5316573 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5316574 (l : real) (s : real -> Prop) (c : real) : (term215 l s c) = (term201 l s c).
Proof. exact (MK_COMB (@lem5316573) (@lem5316572 l s c)). Qed.
Lemma lem5316575 (l : real) (s : real -> Prop) : (term216 l s) = (term202 l s).
Proof. exact (fun_ext (fun c : real => @lem5316574 l s c)). Qed.
Lemma lem5316576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316577 (l : real) (s : real -> Prop) : (term208 l s) = (term203 l s).
Proof. exact (MK_COMB (@lem5316576) (@lem5316575 l s)). Qed.
Lemma lem5316578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5316579 (l : real) (s : real -> Prop) : (term217 l s) = (term218 l s).
Proof. exact (MK_COMB (@lem5316578) (@lem5316577 l s)). Qed.
Lemma lem5316580 (l : real) (s : real -> Prop) (c : real) : (term211 l s c) = (term200 l s c).
Proof. exact (eq_refl (term211 l s c)). Qed.
Lemma lem5316581 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5316582 (l : real) (s : real -> Prop) (x : real -> real) (c : real) : (term219 l s x c) = (term220 l s x c).
Proof. exact (MK_COMB (@lem5316580 l s c) (@lem5316581 x c)). Qed.
Lemma lem5316583 (l : real) (s : real -> Prop) (x : real -> real) (c : real) : (term220 l s x c) = (term221 l s x c).
Proof. exact (eq_refl (term220 l s x c)). Qed.
Lemma lem5316584 (l : real) (s : real -> Prop) (x : real -> real) (c : real) : (term219 l s x c) = (term221 l s x c).
Proof. exact (TRANS (@lem5316582 l s x c) (@lem5316583 l s x c)). Qed.
Lemma lem5316585 (l : real) (s : real -> Prop) (x : real -> real) : (term222 l s x) = (term223 l s x).
Proof. exact (fun_ext (fun c : real => @lem5316584 l s x c)). Qed.
Lemma lem5316586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316587 (l : real) (s : real -> Prop) (x : real -> real) : (term224 l s x) = (term225 l s x).
Proof. exact (MK_COMB (@lem5316586) (@lem5316585 l s x)). Qed.
Lemma lem5316588 (l : real) (s : real -> Prop) : (term226 l s) = (term227 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5316587 l s x)). Qed.
Lemma lem5316589 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5316590 (l : real) (s : real -> Prop) : (term209 l s) = (term228 l s).
Proof. exact (MK_COMB (@lem5316589) (@lem5316588 l s)). Qed.
Lemma lem5316591 (l : real) (s : real -> Prop) : ((term208 l s) = (term209 l s)) = ((term203 l s) = (term228 l s)).
Proof. exact (MK_COMB (@lem5316579 l s) (@lem5316590 l s)). Qed.
Lemma lem5316592 (l : real) (s : real -> Prop) : (term203 l s) = (term228 l s).
Proof. exact (EQ_MP (@lem5316591 l s) (@lem5316566 l s)). Qed.
Lemma lem5316593 (l : real) (s : real -> Prop) : (term182 l s) = (term228 l s).
Proof. exact (TRANS (@lem5316562 l s) (@lem5316592 l s)). Qed.
Lemma lem5316594 (s : real -> Prop) : (term183 s) = (term229 s).
Proof. exact (fun_ext (fun l : real => @lem5316593 l s)). Qed.
Lemma lem5316595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316596 (s : real -> Prop) : (term184 s) = (term230 s).
Proof. exact (MK_COMB (@lem5316595) (@lem5316594 s)). Qed.
Lemma lem5316598 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5316599 (P : type1618) : (term231 P) = (term232 P).
Proof. exact (@lem5316598 real (real -> real) P). Qed.
Lemma lem5316600 (s : real -> Prop) : (term233 s) = (term234 s).
Proof. exact (@lem5316599 (term235 s)). Qed.
Lemma lem5316601 (l : real) (s : real -> Prop) : (term236 s l) = (term227 l s).
Proof. exact (eq_refl (term236 s l)). Qed.
Lemma lem5316602 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5316603 (l : real) (s : real -> Prop) (x : real -> real) : (term237 s l x) = (term238 l s x).
Proof. exact (MK_COMB (@lem5316601 l s) (@lem5316602 x)). Qed.
Lemma lem5316604 (l : real) (s : real -> Prop) (x : real -> real) : (term238 l s x) = (term225 l s x).
Proof. exact (eq_refl (term238 l s x)). Qed.
Lemma lem5316605 (l : real) (s : real -> Prop) (x : real -> real) : (term237 s l x) = (term225 l s x).
Proof. exact (TRANS (@lem5316603 l s x) (@lem5316604 l s x)). Qed.
Lemma lem5316606 (l : real) (s : real -> Prop) : (term239 s l) = (term227 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5316605 l s x)). Qed.
Lemma lem5316607 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5316608 (l : real) (s : real -> Prop) : (term240 s l) = (term228 l s).
Proof. exact (MK_COMB (@lem5316607) (@lem5316606 l s)). Qed.
Lemma lem5316609 (s : real -> Prop) : (term241 s) = (term229 s).
Proof. exact (fun_ext (fun l : real => @lem5316608 l s)). Qed.
Lemma lem5316610 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316611 (s : real -> Prop) : (term233 s) = (term230 s).
Proof. exact (MK_COMB (@lem5316610) (@lem5316609 s)). Qed.
Lemma lem5316612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5316613 (s : real -> Prop) : (term242 s) = (term243 s).
Proof. exact (MK_COMB (@lem5316612) (@lem5316611 s)). Qed.
Lemma lem5316614 (l : real) (s : real -> Prop) : (term236 s l) = (term227 l s).
Proof. exact (eq_refl (term236 s l)). Qed.
Lemma lem5316615 (x : type1627) (l : real) : (x l) = (x l).
Proof. exact (eq_refl (x l)). Qed.
Lemma lem5316616 (s : real -> Prop) (x : type1627) (l : real) : (term244 s x l) = (term245 s x l).
Proof. exact (MK_COMB (@lem5316614 l s) (@lem5316615 x l)). Qed.
Lemma lem5316617 (s : real -> Prop) (x : type1627) (l : real) : (term245 s x l) = (term246 s x l).
Proof. exact (eq_refl (term245 s x l)). Qed.
Lemma lem5316618 (s : real -> Prop) (x : type1627) (l : real) : (term244 s x l) = (term246 s x l).
Proof. exact (TRANS (@lem5316616 s x l) (@lem5316617 s x l)). Qed.
Lemma lem5316619 (s : real -> Prop) (x : type1627) : (term247 s x) = (term248 s x).
Proof. exact (fun_ext (fun l : real => @lem5316618 s x l)). Qed.
Lemma lem5316620 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316621 (s : real -> Prop) (x : type1627) : (term249 s x) = (term250 s x).
Proof. exact (MK_COMB (@lem5316620) (@lem5316619 s x)). Qed.
Lemma lem5316622 (s : real -> Prop) : (term251 s) = (term252 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5316621 s x)). Qed.
Lemma lem5316623 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5316624 (s : real -> Prop) : (term234 s) = (term253 s).
Proof. exact (MK_COMB (@lem5316623) (@lem5316622 s)). Qed.
Lemma lem5316625 (s : real -> Prop) : ((term233 s) = (term234 s)) = ((term230 s) = (term253 s)).
Proof. exact (MK_COMB (@lem5316613 s) (@lem5316624 s)). Qed.
Lemma lem5316626 (s : real -> Prop) : (term230 s) = (term253 s).
Proof. exact (EQ_MP (@lem5316625 s) (@lem5316600 s)). Qed.
Lemma lem5316627 (s : real -> Prop) : (term184 s) = (term253 s).
Proof. exact (TRANS (@lem5316596 s) (@lem5316626 s)). Qed.
Lemma lem5316628 : term185 = term254.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316627 s)). Qed.
Lemma lem5316629 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316630 : term186 = term255.
Proof. exact (MK_COMB (@lem5316629) (@lem5316628)). Qed.
Lemma lem5316632 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5316633 (P : type1016) : (term256 P) = (term257 P).
Proof. exact (@lem5316632 (real -> Prop) type1627 P). Qed.
Lemma lem5316634 : term258 = term259.
Proof. exact (@lem5316633 term260). Qed.
Lemma lem5316635 (s : real -> Prop) : (term261 s) = (term252 s).
Proof. exact (eq_refl (term261 s)). Qed.
Lemma lem5316636 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5316637 (s : real -> Prop) (x : type1627) : (term262 s x) = (term263 s x).
Proof. exact (MK_COMB (@lem5316635 s) (@lem5316636 x)). Qed.
Lemma lem5316638 (s : real -> Prop) (x : type1627) : (term263 s x) = (term250 s x).
Proof. exact (eq_refl (term263 s x)). Qed.
Lemma lem5316639 (s : real -> Prop) (x : type1627) : (term262 s x) = (term250 s x).
Proof. exact (TRANS (@lem5316637 s x) (@lem5316638 s x)). Qed.
Lemma lem5316640 (s : real -> Prop) : (term264 s) = (term252 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5316639 s x)). Qed.
Lemma lem5316641 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5316642 (s : real -> Prop) : (term265 s) = (term253 s).
Proof. exact (MK_COMB (@lem5316641) (@lem5316640 s)). Qed.
Lemma lem5316643 : term266 = term254.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316642 s)). Qed.
Lemma lem5316644 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316645 : term258 = term255.
Proof. exact (MK_COMB (@lem5316644) (@lem5316643)). Qed.
Lemma lem5316646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5316647 : term267 = term268.
Proof. exact (MK_COMB (@lem5316646) (@lem5316645)). Qed.
Lemma lem5316648 (s : real -> Prop) : (term261 s) = (term252 s).
Proof. exact (eq_refl (term261 s)). Qed.
Lemma lem5316649 (x : type1019) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5316650 (x : type1019) (s : real -> Prop) : (term269 x s) = (term270 x s).
Proof. exact (MK_COMB (@lem5316648 s) (@lem5316649 x s)). Qed.
Lemma lem5316651 (x : type1019) (s : real -> Prop) : (term270 x s) = (term271 x s).
Proof. exact (eq_refl (term270 x s)). Qed.
Lemma lem5316652 (x : type1019) (s : real -> Prop) : (term269 x s) = (term271 x s).
Proof. exact (TRANS (@lem5316650 x s) (@lem5316651 x s)). Qed.
Lemma lem5316653 (x : type1019) : (term272 x) = (term273 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316652 x s)). Qed.
Lemma lem5316654 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316655 (x : type1019) : (term274 x) = (term275 x).
Proof. exact (MK_COMB (@lem5316654) (@lem5316653 x)). Qed.
Lemma lem5316656 : term276 = term277.
Proof. exact (fun_ext (fun x : type1019 => @lem5316655 x)). Qed.
Lemma lem5316657 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5316658 : term259 = term278.
Proof. exact (MK_COMB (@lem5316657) (@lem5316656)). Qed.
Lemma lem5316659 : (term258 = term259) = (term255 = term278).
Proof. exact (MK_COMB (@lem5316647) (@lem5316658)). Qed.
Lemma lem5316660 : term255 = term278.
Proof. exact (EQ_MP (@lem5316659) (@lem5316634)). Qed.
Lemma lem5316662 : term186 = term278.
Proof. exact (TRANS (@lem5316630) (@lem5316660)). Qed.
Lemma lem5316663 : term127 = term278.
Proof. exact (TRANS (@lem5316434) (@lem5316662)). Qed.
Lemma lem5316664 (h1 : term127) : term278.
Proof. exact (EQ_MP (@lem5316663) (@lem5316265 h1)). Qed.
Lemma lem5316665 (x : type1019) (h1 : term275 x) : term275 x.
Proof. exact (h1). Qed.
Lemma lem5316666 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term166 l s c.
Proof. exact (h1). Qed.
Lemma lem5316672 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5316717 (x : type1019) (s : real -> Prop) (l : real) (c : real) : (term279 x s l c) = (term279 x s l c).
Proof. exact (eq_refl (term279 x s l c)). Qed.
Lemma lem5316718 (x : type1019) (s : real -> Prop) (l : real) : (term280 x s l) = (term280 x s l).
Proof. exact (fun_ext (fun c : real => @lem5316717 x s l c)). Qed.
Lemma lem5316719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316720 (x : type1019) (s : real -> Prop) (l : real) : (term281 x s l) = (term281 x s l).
Proof. exact (MK_COMB (@lem5316719) (@lem5316718 x s l)). Qed.
Lemma lem5316721 (x : type1019) (s : real -> Prop) : (term282 x s) = (term282 x s).
Proof. exact (fun_ext (fun l : real => @lem5316720 x s l)). Qed.
Lemma lem5316722 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316723 (x : type1019) (s : real -> Prop) : (term271 x s) = (term271 x s).
Proof. exact (MK_COMB (@lem5316722) (@lem5316721 x s)). Qed.
Lemma lem5316724 (x : type1019) : (term273 x) = (term273 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316723 x s)). Qed.
Lemma lem5316725 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316726 (x : type1019) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5316725) (@lem5316724 x)). Qed.
Lemma lem5316727 (x : type1019) (h1 : term275 x) : term275 x.
Proof. exact (EQ_MP (@lem5316726 x) (@lem5316665 x h1)). Qed.
Lemma lem5316744 (s : real -> Prop) (c : real) (x : real) : (term154 s c x) = (term154 s c x).
Proof. exact (eq_refl (term154 s c x)). Qed.
Lemma lem5316745 (s : real -> Prop) (c : real) : (term162 s c) = (term162 s c).
Proof. exact (fun_ext (fun x : real => @lem5316744 s c x)). Qed.
Lemma lem5316746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316747 (s : real -> Prop) (c : real) : (term163 s c) = (term163 s c).
Proof. exact (MK_COMB (@lem5316746) (@lem5316745 s c)). Qed.
Lemma lem5316754 (c : real) (l : real) : (term164 c l) = (term164 c l).
Proof. exact (eq_refl (term164 c l)). Qed.
Lemma lem5316755 (l : real) (s : real -> Prop) (c : real) : (term166 l s c) = (term166 l s c).
Proof. exact (MK_COMB (@lem5316754 c l) (@lem5316747 s c)). Qed.
Lemma lem5316756 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term166 l s c.
Proof. exact (EQ_MP (@lem5316755 l s c) (@lem5316666 l s c h1)). Qed.
Lemma lem5316757 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term163 s c.
Proof. exact (proj2 (@lem5316756 l s c h1)). Qed.
Lemma lem5316762 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5316786 (x : type1019) (s : real -> Prop) (l : real) (c : real) : (term279 x s l c) = (term283 x s l c).
Proof. exact (@lem19490 (term284 x l c s) (term175 s c l) (term285 x s l c)). Qed.
Lemma lem5316787 (x : type1019) (s : real -> Prop) (l : real) : (term280 x s l) = (term286 x s l).
Proof. exact (fun_ext (fun c : real => @lem5316786 x s l c)). Qed.
Lemma lem5316788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316789 (x : type1019) (s : real -> Prop) (l : real) : (term281 x s l) = (term287 x s l).
Proof. exact (MK_COMB (@lem5316788) (@lem5316787 x s l)). Qed.
Lemma lem5316790 (x : type1019) (s : real -> Prop) : (term282 x s) = (term288 x s).
Proof. exact (fun_ext (fun l : real => @lem5316789 x s l)). Qed.
Lemma lem5316791 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316792 (x : type1019) (s : real -> Prop) : (term271 x s) = (term289 x s).
Proof. exact (MK_COMB (@lem5316791) (@lem5316790 x s)). Qed.
Lemma lem5316793 (x : type1019) : (term273 x) = (term290 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5316792 x s)). Qed.
Lemma lem5316794 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5316796 (x : type1019) : (term275 x) = (term291 x).
Proof. exact (MK_COMB (@lem5316794) (@lem5316793 x)). Qed.
Lemma lem5316797 (x : type1019) (h1 : term275 x) : term291 x.
Proof. exact (EQ_MP (@lem5316796 x) (@lem5316727 x h1)). Qed.
Lemma lem5316809 (s : real -> Prop) (c : real) (x : real) : (term154 s c x) = (term154 s c x).
Proof. exact (eq_refl (term154 s c x)). Qed.
Lemma lem5316810 (s : real -> Prop) (c : real) : (term162 s c) = (term162 s c).
Proof. exact (fun_ext (fun x : real => @lem5316809 s c x)). Qed.
Lemma lem5316811 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5316813 (s : real -> Prop) (c : real) : (term163 s c) = (term163 s c).
Proof. exact (MK_COMB (@lem5316811) (@lem5316810 s c)). Qed.
Lemma lem5316814 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term163 s c.
Proof. exact (EQ_MP (@lem5316813 s c) (@lem5316757 l s c h1)). Qed.
Lemma lem5316815 (_69684 : real -> Prop) (x : type1019) (h1 : term275 x) : term292 x _69684.
Proof. exact (@lem5316797 x h1 _69684). Qed.
Lemma lem5316816 (x : type1019) (_69684 : real -> Prop) : (term292 x _69684) = (term289 x _69684).
Proof. exact (eq_refl (term292 x _69684)). Qed.
Lemma lem5316817 (_69684 : real -> Prop) (x : type1019) (h1 : term275 x) : term289 x _69684.
Proof. exact (EQ_MP (@lem5316816 x _69684) (@lem5316815 _69684 x h1)). Qed.
Lemma lem5316818 (_69684 : real -> Prop) (_69685 : real) (x : type1019) (h1 : term275 x) : term293 x _69684 _69685.
Proof. exact (@lem5316817 _69684 x h1 _69685). Qed.
Lemma lem5316819 (x : type1019) (_69684 : real -> Prop) (_69685 : real) : (term293 x _69684 _69685) = (term287 x _69684 _69685).
Proof. exact (eq_refl (term293 x _69684 _69685)). Qed.
Lemma lem5316820 (_69684 : real -> Prop) (_69685 : real) (x : type1019) (h1 : term275 x) : term287 x _69684 _69685.
Proof. exact (EQ_MP (@lem5316819 x _69684 _69685) (@lem5316818 _69684 _69685 x h1)). Qed.
Lemma lem5316821 (_69684 : real -> Prop) (_69685 : real) (_69686 : real) (x : type1019) (h1 : term275 x) : term294 x _69684 _69685 _69686.
Proof. exact (@lem5316820 _69684 _69685 x h1 _69686). Qed.
Lemma lem5316822 (x : type1019) (_69684 : real -> Prop) (_69685 : real) (_69686 : real) : (term294 x _69684 _69685 _69686) = (term283 x _69684 _69685 _69686).
Proof. exact (eq_refl (term294 x _69684 _69685 _69686)). Qed.
Lemma lem5316823 (_69684 : real -> Prop) (_69685 : real) (_69686 : real) (x : type1019) (h1 : term275 x) : term283 x _69684 _69685 _69686.
Proof. exact (EQ_MP (@lem5316822 x _69684 _69685 _69686) (@lem5316821 _69684 _69685 _69686 x h1)). Qed.
Lemma lem5316824 (_69687 : real) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term295 s c _69687.
Proof. exact (@lem5316814 l s c h1 _69687). Qed.
Lemma lem5316825 (s : real -> Prop) (c : real) (_69687 : real) : (term295 s c _69687) = (term154 s c _69687).
Proof. exact (eq_refl (term295 s c _69687)). Qed.
Lemma lem5316827 (_69684 : real -> Prop) (_69685 : real) (_69686 : real) (x : type1019) (h1 : term275 x) : term296 x _69684 _69685 _69686.
Proof. exact (proj2 (@lem5316823 _69684 _69685 _69686 x h1)). Qed.
Lemma lem5316828 (_69685 : real) (_69686 : real) (_69684 : real -> Prop) (x : type1019) (h1 : term275 x) : term297 x _69685 _69686 _69684.
Proof. exact (proj1 (@lem5316823 _69684 _69685 _69686 x h1)). Qed.
Lemma lem5316830 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5316838 (_69687 : real) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term154 s c _69687.
Proof. exact (EQ_MP (@lem5316825 s c _69687) (@lem5316824 _69687 l s c h1)). Qed.
Lemma lem5316849 (x : type1019) (_69685 : real) (_69686 : real) (_69684 : real -> Prop) : (term297 x _69685 _69686 _69684) = (term298 x _69685 _69686 _69684).
Proof. exact (@lem5315226 (term83 _69684 _69685) (term0 _69686 _69685) (term284 x _69685 _69686 _69684)). Qed.
Lemma lem5316850 (_69685 : real) (_69686 : real) (_69684 : real -> Prop) (x : type1019) (h1 : term275 x) : term298 x _69685 _69686 _69684.
Proof. exact (EQ_MP (@lem5316849 x _69685 _69686 _69684) (@lem5316828 _69685 _69686 _69684 x h1)). Qed.
Lemma lem5316861 (x : type1019) (_69684 : real -> Prop) (_69685 : real) (_69686 : real) : (term296 x _69684 _69685 _69686) = (term299 x _69684 _69685 _69686).
Proof. exact (@lem5315226 (term83 _69684 _69685) (term0 _69686 _69685) (term285 x _69684 _69685 _69686)). Qed.
Lemma lem5316862 (_69684 : real -> Prop) (_69685 : real) (_69686 : real) (x : type1019) (h1 : term275 x) : term299 x _69684 _69685 _69686.
Proof. exact (EQ_MP (@lem5316861 x _69684 _69685 _69686) (@lem5316827 _69684 _69685 _69686 x h1)). Qed.
Lemma lem5316864 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5316865 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term86 s l.
Proof. exact (fun h0 : term83 s l => @lem5316864 s l h1). Qed.
Lemma lem5316867 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5316868 (s : real -> Prop) (l : real) : (term86 s l) = (has_sup s l).
Proof. exact (@lem5316867 (has_sup s l)). Qed.
Lemma lem5316869 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (EQ_MP (@lem5316868 s l) (@lem5316865 s l h1)). Qed.
Lemma lem5316871 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt c l.
Proof. exact (proj1 (@lem5316756 l s c h1)). Qed.
Lemma lem5316872 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term300 c l.
Proof. exact (fun h0 : term0 c l => @lem5316871 l s c h1). Qed.
Lemma lem5316874 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5316875 (c : real) (l : real) : (term300 c l) = (real_lt c l).
Proof. exact (@lem5316874 (real_lt c l)). Qed.
Lemma lem5316876 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt c l.
Proof. exact (EQ_MP (@lem5316875 c l) (@lem5316872 l s c h1)). Qed.
Lemma lem5316892 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5316893 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term301 x _69685 _69686 _69684) = (term302 x _69684 _69686 _69685).
Proof. exact (@lem5316892 (term284 x _69685 _69686 _69684) (term0 _69686 _69685)). Qed.
Lemma lem5316899 (_69684 : real -> Prop) (_69685 : real) : (term303 _69684 _69685) = (term303 _69684 _69685).
Proof. exact (eq_refl (term303 _69684 _69685)). Qed.
Lemma lem5316900 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term298 x _69685 _69686 _69684) = (term304 x _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5316899 _69684 _69685) (@lem5316893 x _69684 _69686 _69685)). Qed.
Lemma lem5316904 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5316905 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term304 x _69684 _69686 _69685) = (term305 x _69684 _69686 _69685).
Proof. exact (@lem5316904 (term284 x _69685 _69686 _69684) (term83 _69684 _69685) (term0 _69686 _69685)). Qed.
Lemma lem5316921 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term298 x _69685 _69686 _69684) = (term305 x _69684 _69686 _69685).
Proof. exact (TRANS (@lem5316900 x _69684 _69686 _69685) (@lem5316905 x _69684 _69686 _69685)). Qed.
Lemma lem5316922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5316923 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term306 x _69685 _69686 _69684) = (term307 x _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5316922) (@lem5316921 x _69684 _69686 _69685)). Qed.
Lemma lem5316939 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term305 x _69684 _69686 _69685) = (term305 x _69684 _69686 _69685).
Proof. exact (eq_refl (term305 x _69684 _69686 _69685)). Qed.
Lemma lem5316940 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : ((term298 x _69685 _69686 _69684) = (term305 x _69684 _69686 _69685)) = ((term305 x _69684 _69686 _69685) = (term305 x _69684 _69686 _69685)).
Proof. exact (MK_COMB (@lem5316923 x _69684 _69686 _69685) (@lem5316939 x _69684 _69686 _69685)). Qed.
Lemma lem5316942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5316943 (x : Prop) : (x = x) = True.
Proof. exact (@lem5316942 Prop x). Qed.
Lemma lem5316944 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : ((term305 x _69684 _69686 _69685) = (term305 x _69684 _69686 _69685)) = True.
Proof. exact (@lem5316943 (term305 x _69684 _69686 _69685)). Qed.
Lemma lem5316945 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : ((term298 x _69685 _69686 _69684) = (term305 x _69684 _69686 _69685)) = True.
Proof. exact (TRANS (@lem5316940 x _69684 _69686 _69685) (@lem5316944 x _69684 _69686 _69685)). Qed.
Lemma lem5316946 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : True = ((term298 x _69685 _69686 _69684) = (term305 x _69684 _69686 _69685)).
Proof. exact (SYM (@lem5316945 x _69684 _69686 _69685)). Qed.
Lemma lem5316947 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term298 x _69685 _69686 _69684) = (term305 x _69684 _69686 _69685).
Proof. exact (EQ_MP (@lem5316946 x _69684 _69686 _69685) (@lem0)). Qed.
Lemma lem5316948 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) (x : type1019) (h1 : term275 x) : term305 x _69684 _69686 _69685.
Proof. exact (EQ_MP (@lem5316947 x _69684 _69686 _69685) (@lem5316850 _69685 _69686 _69684 x h1)). Qed.
Lemma lem5316950 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5316951 (x : type1019) (_69685 : real) (_69686 : real) (_69684 : real -> Prop) : (term305 x _69684 _69686 _69685) = (term308 x _69685 _69686 _69684).
Proof. exact (@lem5316950 (term175 _69684 _69686 _69685) (term284 x _69685 _69686 _69684)). Qed.
Lemma lem5316953 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5316954 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term309 _69684 _69686 _69685) = (term310 _69684 _69686 _69685).
Proof. exact (@lem5316953 (term83 _69684 _69685) (term0 _69686 _69685)). Qed.
Lemma lem5316956 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5316957 (_69684 : real -> Prop) (_69685 : real) : (term107 _69684 _69685) = (has_sup _69684 _69685).
Proof. exact (@lem5316956 (has_sup _69684 _69685)). Qed.
Lemma lem5316958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5316959 (_69684 : real -> Prop) (_69685 : real) : (term108 _69684 _69685) = (term109 _69684 _69685).
Proof. exact (MK_COMB (@lem5316958) (@lem5316957 _69684 _69685)). Qed.
Lemma lem5316961 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5316962 (_69686 : real) (_69685 : real) : (term311 _69686 _69685) = (real_lt _69686 _69685).
Proof. exact (@lem5316961 (real_lt _69686 _69685)). Qed.
Lemma lem5316963 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term310 _69684 _69686 _69685) = (term180 _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5316959 _69684 _69685) (@lem5316962 _69686 _69685)). Qed.
Lemma lem5316964 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term309 _69684 _69686 _69685) = (term180 _69684 _69686 _69685).
Proof. exact (TRANS (@lem5316954 _69684 _69686 _69685) (@lem5316963 _69684 _69686 _69685)). Qed.
Lemma lem5316965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5316966 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term312 _69684 _69686 _69685) = (term143 _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5316965) (@lem5316964 _69684 _69686 _69685)). Qed.
Lemma lem5316967 (x : type1019) (_69685 : real) (_69686 : real) (_69684 : real -> Prop) : (term284 x _69685 _69686 _69684) = (term284 x _69685 _69686 _69684).
Proof. exact (eq_refl (term284 x _69685 _69686 _69684)). Qed.
Lemma lem5316968 (x : type1019) (_69685 : real) (_69686 : real) (_69684 : real -> Prop) : (term308 x _69685 _69686 _69684) = (term313 x _69685 _69686 _69684).
Proof. exact (MK_COMB (@lem5316966 _69684 _69686 _69685) (@lem5316967 x _69685 _69686 _69684)). Qed.
Lemma lem5316969 (x : type1019) (_69685 : real) (_69686 : real) (_69684 : real -> Prop) : (term305 x _69684 _69686 _69685) = (term313 x _69685 _69686 _69684).
Proof. exact (TRANS (@lem5316951 x _69685 _69686 _69684) (@lem5316968 x _69685 _69686 _69684)). Qed.
Lemma lem5316971 (c : real) (s : real -> Prop) (l : real) (h1 : term166 l s c) (h2 : has_sup s l) : term180 s c l.
Proof. exact (conj (@lem5316869 s l h2) (@lem5316876 l s c h1)). Qed.
Lemma lem5316973 (_69685 : real) (_69686 : real) (_69684 : real -> Prop) (x : type1019) (h1 : term275 x) : term313 x _69685 _69686 _69684.
Proof. exact (EQ_MP (@lem5316969 x _69685 _69686 _69684) (@lem5316948 _69684 _69686 _69685 x h1)). Qed.
Lemma lem5316974 (l : real) (c : real) (s : real -> Prop) (x : type1019) (h1 : term275 x) : term313 x l c s.
Proof. exact (@lem5316973 l c s x h1). Qed.
Lemma lem5316977 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term284 x l c s.
Proof. exact (@lem5316974 l c s x h1 (@lem5316971 c s l h2 h3)). Qed.
Lemma lem5316978 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term314 x l c s.
Proof. exact (fun h0 : term315 x l c s => @lem5316977 x c s l h1 h2 h3). Qed.
Lemma lem5316980 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5316981 (x : type1019) (l : real) (c : real) (s : real -> Prop) : (term314 x l c s) = (term284 x l c s).
Proof. exact (@lem5316980 (term284 x l c s)). Qed.
Lemma lem5316982 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term284 x l c s.
Proof. exact (EQ_MP (@lem5316981 x l c s) (@lem5316978 x c s l h1 h2 h3)). Qed.
Lemma lem5316984 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (h1). Qed.
Lemma lem5316985 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term86 s l.
Proof. exact (fun h0 : term83 s l => @lem5316984 s l h1). Qed.
Lemma lem5316987 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5316988 (s : real -> Prop) (l : real) : (term86 s l) = (has_sup s l).
Proof. exact (@lem5316987 (has_sup s l)). Qed.
Lemma lem5316989 (s : real -> Prop) (l : real) (h1 : has_sup s l) : has_sup s l.
Proof. exact (EQ_MP (@lem5316988 s l) (@lem5316985 s l h1)). Qed.
Lemma lem5316991 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt c l.
Proof. exact (proj1 (@lem5316756 l s c h1)). Qed.
Lemma lem5316992 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term300 c l.
Proof. exact (fun h0 : term0 c l => @lem5316991 l s c h1). Qed.
Lemma lem5316994 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5316995 (c : real) (l : real) : (term300 c l) = (real_lt c l).
Proof. exact (@lem5316994 (real_lt c l)). Qed.
Lemma lem5316996 (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : real_lt c l.
Proof. exact (EQ_MP (@lem5316995 c l) (@lem5316992 l s c h1)). Qed.
Lemma lem5317012 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5317013 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term316 x _69684 _69685 _69686) = (term317 x _69684 _69686 _69685).
Proof. exact (@lem5317012 (term285 x _69684 _69685 _69686) (term0 _69686 _69685)). Qed.
Lemma lem5317019 (_69684 : real -> Prop) (_69685 : real) : (term303 _69684 _69685) = (term303 _69684 _69685).
Proof. exact (eq_refl (term303 _69684 _69685)). Qed.
Lemma lem5317020 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term299 x _69684 _69685 _69686) = (term318 x _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5317019 _69684 _69685) (@lem5317013 x _69684 _69686 _69685)). Qed.
Lemma lem5317024 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term16 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5317025 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term318 x _69684 _69686 _69685) = (term319 x _69684 _69686 _69685).
Proof. exact (@lem5317024 (term285 x _69684 _69685 _69686) (term83 _69684 _69685) (term0 _69686 _69685)). Qed.
Lemma lem5317041 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term299 x _69684 _69685 _69686) = (term319 x _69684 _69686 _69685).
Proof. exact (TRANS (@lem5317020 x _69684 _69686 _69685) (@lem5317025 x _69684 _69686 _69685)). Qed.
Lemma lem5317042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5317043 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term320 x _69684 _69685 _69686) = (term321 x _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5317042) (@lem5317041 x _69684 _69686 _69685)). Qed.
Lemma lem5317059 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term319 x _69684 _69686 _69685) = (term319 x _69684 _69686 _69685).
Proof. exact (eq_refl (term319 x _69684 _69686 _69685)). Qed.
Lemma lem5317060 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : ((term299 x _69684 _69685 _69686) = (term319 x _69684 _69686 _69685)) = ((term319 x _69684 _69686 _69685) = (term319 x _69684 _69686 _69685)).
Proof. exact (MK_COMB (@lem5317043 x _69684 _69686 _69685) (@lem5317059 x _69684 _69686 _69685)). Qed.
Lemma lem5317062 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5317063 (x : Prop) : (x = x) = True.
Proof. exact (@lem5317062 Prop x). Qed.
Lemma lem5317064 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : ((term319 x _69684 _69686 _69685) = (term319 x _69684 _69686 _69685)) = True.
Proof. exact (@lem5317063 (term319 x _69684 _69686 _69685)). Qed.
Lemma lem5317065 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : ((term299 x _69684 _69685 _69686) = (term319 x _69684 _69686 _69685)) = True.
Proof. exact (TRANS (@lem5317060 x _69684 _69686 _69685) (@lem5317064 x _69684 _69686 _69685)). Qed.
Lemma lem5317066 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : True = ((term299 x _69684 _69685 _69686) = (term319 x _69684 _69686 _69685)).
Proof. exact (SYM (@lem5317065 x _69684 _69686 _69685)). Qed.
Lemma lem5317067 (x : type1019) (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term299 x _69684 _69685 _69686) = (term319 x _69684 _69686 _69685).
Proof. exact (EQ_MP (@lem5317066 x _69684 _69686 _69685) (@lem0)). Qed.
Lemma lem5317068 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) (x : type1019) (h1 : term275 x) : term319 x _69684 _69686 _69685.
Proof. exact (EQ_MP (@lem5317067 x _69684 _69686 _69685) (@lem5316862 _69684 _69685 _69686 x h1)). Qed.
Lemma lem5317070 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5317071 (x : type1019) (_69684 : real -> Prop) (_69685 : real) (_69686 : real) : (term319 x _69684 _69686 _69685) = (term322 x _69684 _69685 _69686).
Proof. exact (@lem5317070 (term175 _69684 _69686 _69685) (term285 x _69684 _69685 _69686)). Qed.
Lemma lem5317073 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5317074 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term309 _69684 _69686 _69685) = (term310 _69684 _69686 _69685).
Proof. exact (@lem5317073 (term83 _69684 _69685) (term0 _69686 _69685)). Qed.
Lemma lem5317076 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5317077 (_69684 : real -> Prop) (_69685 : real) : (term107 _69684 _69685) = (has_sup _69684 _69685).
Proof. exact (@lem5317076 (has_sup _69684 _69685)). Qed.
Lemma lem5317078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5317079 (_69684 : real -> Prop) (_69685 : real) : (term108 _69684 _69685) = (term109 _69684 _69685).
Proof. exact (MK_COMB (@lem5317078) (@lem5317077 _69684 _69685)). Qed.
Lemma lem5317081 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5317082 (_69686 : real) (_69685 : real) : (term311 _69686 _69685) = (real_lt _69686 _69685).
Proof. exact (@lem5317081 (real_lt _69686 _69685)). Qed.
Lemma lem5317083 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term310 _69684 _69686 _69685) = (term180 _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5317079 _69684 _69685) (@lem5317082 _69686 _69685)). Qed.
Lemma lem5317084 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term309 _69684 _69686 _69685) = (term180 _69684 _69686 _69685).
Proof. exact (TRANS (@lem5317074 _69684 _69686 _69685) (@lem5317083 _69684 _69686 _69685)). Qed.
Lemma lem5317085 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5317086 (_69684 : real -> Prop) (_69686 : real) (_69685 : real) : (term312 _69684 _69686 _69685) = (term143 _69684 _69686 _69685).
Proof. exact (MK_COMB (@lem5317085) (@lem5317084 _69684 _69686 _69685)). Qed.
Lemma lem5317087 (x : type1019) (_69684 : real -> Prop) (_69685 : real) (_69686 : real) : (term285 x _69684 _69685 _69686) = (term285 x _69684 _69685 _69686).
Proof. exact (eq_refl (term285 x _69684 _69685 _69686)). Qed.
Lemma lem5317088 (x : type1019) (_69684 : real -> Prop) (_69685 : real) (_69686 : real) : (term322 x _69684 _69685 _69686) = (term323 x _69684 _69685 _69686).
Proof. exact (MK_COMB (@lem5317086 _69684 _69686 _69685) (@lem5317087 x _69684 _69685 _69686)). Qed.
Lemma lem5317089 (x : type1019) (_69684 : real -> Prop) (_69685 : real) (_69686 : real) : (term319 x _69684 _69686 _69685) = (term323 x _69684 _69685 _69686).
Proof. exact (TRANS (@lem5317071 x _69684 _69685 _69686) (@lem5317088 x _69684 _69685 _69686)). Qed.
Lemma lem5317091 (c : real) (s : real -> Prop) (l : real) (h1 : term166 l s c) (h2 : has_sup s l) : term180 s c l.
Proof. exact (conj (@lem5316989 s l h2) (@lem5316996 l s c h1)). Qed.
Lemma lem5317093 (_69684 : real -> Prop) (_69685 : real) (_69686 : real) (x : type1019) (h1 : term275 x) : term323 x _69684 _69685 _69686.
Proof. exact (EQ_MP (@lem5317089 x _69684 _69685 _69686) (@lem5317068 _69684 _69686 _69685 x h1)). Qed.
Lemma lem5317094 (s : real -> Prop) (l : real) (c : real) (x : type1019) (h1 : term275 x) : term323 x s l c.
Proof. exact (@lem5317093 s l c x h1). Qed.
Lemma lem5317097 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term285 x s l c.
Proof. exact (@lem5317094 s l c x h1 (@lem5317091 c s l h2 h3)). Qed.
Lemma lem5317098 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term324 x s l c.
Proof. exact (fun h0 : term325 x s l c => @lem5317097 x c s l h1 h2 h3). Qed.
Lemma lem5317100 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5317101 (x : type1019) (s : real -> Prop) (l : real) (c : real) : (term324 x s l c) = (term285 x s l c).
Proof. exact (@lem5317100 (term285 x s l c)). Qed.
Lemma lem5317102 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term285 x s l c.
Proof. exact (EQ_MP (@lem5317101 x s l c) (@lem5317098 x c s l h1 h2 h3)). Qed.
Lemma lem5317104 (a : Prop) (b : Prop) : (term326 a b) = (term327 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5317105 (s : real -> Prop) (c : real) (_69687 : real) : (term154 s c _69687) = (term153 s c _69687).
Proof. exact (@lem5317104 (@IN real _69687 s) (real_lt c _69687)). Qed.
Lemma lem5317107 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5317108 (s : real -> Prop) (c : real) (_69687 : real) : (term153 s c _69687) = (term328 s c _69687).
Proof. exact (@lem5317107 (term140 s c _69687)). Qed.
Lemma lem5317109 (s : real -> Prop) (c : real) (_69687 : real) : (term154 s c _69687) = (term328 s c _69687).
Proof. exact (TRANS (@lem5317105 s c _69687) (@lem5317108 s c _69687)). Qed.
Lemma lem5317111 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term329 x s l c.
Proof. exact (conj (@lem5316982 x c s l h1 h2 h3) (@lem5317102 x c s l h1 h2 h3)). Qed.
Lemma lem5317113 (_69687 : real) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term328 s c _69687.
Proof. exact (EQ_MP (@lem5317109 s c _69687) (@lem5316838 _69687 l s c h1)). Qed.
Lemma lem5317114 (x : type1019) (l : real) (s : real -> Prop) (c : real) (h1 : term166 l s c) : term330 x s l c.
Proof. exact (@lem5317113 (x s l c) l s c h1). Qed.
Lemma lem5317117 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (@lem5317114 x l s c h2 (@lem5317111 x c s l h1 h2 h3)). Qed.
Lemma lem5317118 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : term115.
Proof. exact (fun h0 : ~ False => @lem5317117 x c s l h1 h2 h3). Qed.
Lemma lem5317120 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5317121 : term115 = False.
Proof. exact (@lem5317120 False). Qed.
Lemma lem5317122 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317121) (@lem5317118 x c s l h1 h2 h3)). Qed.
Lemma lem5317123 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5317122 x c s l h1 h2 h3) (fun h4 : False => @lem5316830 s l h3)). Qed.
Lemma lem5317124 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317123 x c s l h1 h2 h3) (@lem5316830 s l h3)). Qed.
Lemma lem5317125 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5317124 x c s l h1 h2 h3) (fun h4 : False => @lem5316762 s l h3)). Qed.
Lemma lem5317126 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317125 x c s l h1 h2 h3) (@lem5316762 s l h3)). Qed.
Lemma lem5317127 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5317126 x c s l h1 h2 h3) (fun h4 : False => @lem5316762 s l h3)). Qed.
Lemma lem5317128 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317127 x c s l h1 h2 h3) (@lem5316762 s l h3)). Qed.
Lemma lem5317129 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : (term166 l s c) = False.
Proof. exact (prop_ext (fun h4 : term166 l s c => @lem5317128 x c s l h1 h2 h3) (fun h4 : False => @lem5316756 l s c h2)). Qed.
Lemma lem5317130 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317129 x c s l h1 h2 h3) (@lem5316756 l s c h2)). Qed.
Lemma lem5317131 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : (term275 x) = False.
Proof. exact (prop_ext (fun h4 : term275 x => @lem5317130 x c s l h1 h2 h3) (fun h4 : False => @lem5316727 x h1)). Qed.
Lemma lem5317132 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317131 x c s l h1 h2 h3) (@lem5316727 x h1)). Qed.
Lemma lem5317133 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5317132 x c s l h1 h2 h3) (fun h4 : False => @lem5316672 s l h3)). Qed.
Lemma lem5317134 (x : type1019) (c : real) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term166 l s c) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317133 x c s l h1 h2 h3) (@lem5316672 s l h3)). Qed.
Lemma lem5317135 (x : type1019) (s : real -> Prop) (l : real) (h1 : term275 x) (h2 : term120 l s) (h3 : has_sup s l) : False.
Proof. exact (ex_elim (@lem5316405 l s h2) (fun c : real => fun h0 : term172 l s c => @lem5317134 x c s l h1 h0 h3)). Qed.
Lemma lem5317136 (s : real -> Prop) (l : real) (h1 : term127) (h2 : term120 l s) (h3 : has_sup s l) : False.
Proof. exact (ex_elim (@lem5316664 h1) (fun x : type1019 => fun h0 : term277 x => @lem5317135 x s l h0 h2 h3)). Qed.
Lemma lem5317137 (s : real -> Prop) (l : real) (h1 : term127) (h2 : term120 l s) (h3 : has_sup s l) : (has_sup s l) = False.
Proof. exact (prop_ext (fun h4 : has_sup s l => @lem5317136 s l h1 h2 h3) (fun h4 : False => @lem5316271 s l h3)). Qed.
Lemma lem5317138 (s : real -> Prop) (l : real) (h1 : term127) (h2 : term120 l s) (h3 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317137 s l h1 h2 h3) (@lem5316271 s l h3)). Qed.
Lemma lem5317139 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_sup s l) : term125.
Proof. exact (fun h0 : term127 => @lem5317138 s l h0 h1 h2). Qed.
Lemma lem5317140 : term125 = term126.
Proof. exact (@lem69 term127). Qed.
Lemma lem5317141 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_sup s l) : term126.
Proof. exact (EQ_MP (@lem5317140) (@lem5317139 s l h1 h2)). Qed.
Lemma lem5317142 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term130 l s.
Proof. exact (fun h0 : term120 l s => @lem5317141 s l h0 h1). Qed.
Lemma lem5317143 (l : real) (s : real -> Prop) : term131 l s.
Proof. exact (fun h0 : has_sup s l => @lem5317142 s l h0). Qed.
Lemma lem5317148 (s : real -> Prop) : term135 s.
Proof. exact (fun l : real => @lem5317143 l s). Qed.
Lemma lem5317153 : term139.
Proof. exact (fun s : real -> Prop => @lem5317148 s). Qed.
Lemma lem5317154 : term138.
Proof. exact (EQ_MP (@lem5316262) (@lem5317153)). Qed.
Lemma lem5317155 (s : real -> Prop) : term331 s.
Proof. exact (@lem5317154 s). Qed.
Lemma lem5317156 (s : real -> Prop) : (term331 s) = (term134 s).
Proof. exact (eq_refl (term331 s)). Qed.
Lemma lem5317157 (s : real -> Prop) : term134 s.
Proof. exact (EQ_MP (@lem5317156 s) (@lem5317155 s)). Qed.
Lemma lem5317158 (s : real -> Prop) (l : real) : term332 s l.
Proof. exact (@lem5317157 s l). Qed.
Lemma lem5317159 (l : real) (s : real -> Prop) : (term332 s l) = (term121 l s).
Proof. exact (eq_refl (term332 s l)). Qed.
Lemma lem5317160 (l : real) (s : real -> Prop) : term121 l s.
Proof. exact (EQ_MP (@lem5317159 l s) (@lem5317158 s l)). Qed.
Lemma lem5317162 (l : real) (s : real -> Prop) : term121 l s.
Proof. exact (@lem5315976 l s (@lem5317160 l s)). Qed.
Lemma lem5317163 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term129 l s.
Proof. exact (@lem5317162 l s (@lem5315243 s l h1)). Qed.
Lemma lem5317164 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_sup s l) : term125.
Proof. exact (@lem5317163 s l h2 (@lem5315961 l s h1)). Qed.
Lemma lem5317165 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_sup s l) : False.
Proof. exact (@lem5317164 s l h1 h2 (@lem5311014)). Qed.
Lemma lem5317166 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_sup s l) : (term120 l s) = False.
Proof. exact (prop_ext (fun h3 : term120 l s => @lem5317165 s l h1 h2) (fun h3 : False => @lem5315961 l s h1)). Qed.
Lemma lem5317167 (s : real -> Prop) (l : real) (h1 : term120 l s) (h2 : has_sup s l) : False.
Proof. exact (EQ_MP (@lem5317166 s l h1 h2) (@lem5315961 l s h1)). Qed.
Lemma lem5317168 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term119 l s.
Proof. exact (fun h0 : term120 l s => @lem5317167 s l h0 h1). Qed.
Lemma lem5317169 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term118 l s.
Proof. exact (EQ_MP (@lem5315960 l s) (@lem5317168 s l h1)). Qed.
Lemma lem5317170 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term333 l s.
Proof. exact (conj (@lem5315956 s l h1) (@lem5317169 s l h1)). Qed.
Lemma lem5317171 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term334 l s.
Proof. exact (conj (@lem5315292 s l h1) (@lem5317170 s l h1)). Qed.
Lemma lem5317172 (s : real -> Prop) (l : real) (h1 : has_sup s l) : (has_sup s l) = (term334 l s).
Proof. exact (prop_ext (fun h2 : has_sup s l => @lem5317171 s l h1) (fun h2 : term334 l s => @lem5315243 s l h1)). Qed.
Lemma lem5317173 (s : real -> Prop) (l : real) (h1 : has_sup s l) : term334 l s.
Proof. exact (EQ_MP (@lem5317172 s l h1) (@lem5315243 s l h1)). Qed.
Lemma lem5317174 (l : real) (s : real -> Prop) : term335 l s.
Proof. exact (fun h0 : has_sup s l => @lem5317173 s l h0). Qed.
Lemma lem5317175 (l : real) (s : real -> Prop) (h1 : term334 l s) : term334 l s.
Proof. exact (h1). Qed.
Lemma lem5317176 (l : real) (s : real -> Prop) (h1 : term333 l s) : term333 l s.
Proof. exact (h1). Qed.
Lemma lem5317177 (s : real -> Prop) (h1 : term22 s) : term22 s.
Proof. exact (h1). Qed.
Lemma lem5317178 (l : real) (s : real -> Prop) (h1 : term118 l s) : term118 l s.
Proof. exact (h1). Qed.
Lemma lem5317179 (s : real -> Prop) (l : real) (h1 : term25 s l) : term25 s l.
Proof. exact (h1). Qed.
Lemma lem5317180 (s : real -> Prop) : term336 s.
Proof. exact (@lem5291214 s). Qed.
Lemma lem5317181 (s : real -> Prop) : (term336 s) = (term337 s).
Proof. exact (eq_refl (term336 s)). Qed.
Lemma lem5317182 (s : real -> Prop) : term337 s.
Proof. exact (EQ_MP (@lem5317181 s) (@lem5317180 s)). Qed.
Lemma lem5317183 (s : real -> Prop) (b : real) : term338 s b.
Proof. exact (@lem5317182 s b). Qed.
Lemma lem5317184 (s : real -> Prop) (b : real) : (term338 s b) = ((has_sup s b) = (term339 s b)).
Proof. exact (eq_refl (term338 s b)). Qed.
Lemma lem5317210 (s : real -> Prop) (b : real) : (has_sup s b) = (term339 s b).
Proof. exact (EQ_MP (@lem5317184 s b) (@lem5317183 s b)). Qed.
Lemma lem5317211 (s : real -> Prop) (l : real) : (has_sup s l) = (term339 s l).
Proof. exact (@lem5317210 s l). Qed.
Lemma lem5317224 (s : real -> Prop) (l : real) : (term339 s l) = (has_sup s l).
Proof. exact (SYM (@lem5317211 s l)). Qed.
Lemma lem5317225 (s : real -> Prop) (c : real) (h1 : term25 s c) : term25 s c.
Proof. exact (h1). Qed.
Lemma lem5317227 (x : real) (y : real) : (real_le y x) = (term0 x y).
Proof. exact (EQ_MP (@lem5315215 x y) (@lem5315214 x y)). Qed.
Lemma lem5317228 (c : real) (l : real) : (real_le l c) = (term0 c l).
Proof. exact (@lem5317227 c l). Qed.
Lemma lem5317229 (l : real) (c : real) : (term0 c l) = (real_le l c).
Proof. exact (SYM (@lem5317228 c l)). Qed.
Lemma lem5317230 (c : real) (l : real) (h1 : real_lt c l) : real_lt c l.
Proof. exact (h1). Qed.
Lemma lem5317231 (c : real) (l : real) (s : real -> Prop) (h1 : term118 l s) : term340 s l c.
Proof. exact (@lem5317178 l s h1 (term341 l c)). Qed.
Lemma lem5317232 (s : real -> Prop) (l : real) (c : real) : (term340 s l c) = (term342 s l c).
Proof. exact (eq_refl (term340 s l c)). Qed.
Lemma lem5317233 (c : real) (l : real) (s : real -> Prop) (h1 : term118 l s) : term342 s l c.
Proof. exact (EQ_MP (@lem5317232 s l c) (@lem5317231 c l s h1)). Qed.
Lemma lem5317235 (p : Prop) (q : Prop) (r : Prop) : term343 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5317236 (s : real -> Prop) (l : real) (c : real) : term344 s l c.
Proof. exact (@lem5317235 (term345 c l) (term346 s l c) False). Qed.
Lemma lem5317252 (c : real) (l : real) : (term347 c l) = (term348 c l).
Proof. exact (@lem17362 (real_lt c l) (term345 c l)). Qed.
Lemma lem5317254 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5317255 (s : real -> Prop) (c : real) (l : real) : (term350 s c l) = (term351 s c l).
Proof. exact (MK_COMB (@lem5317254 s) (@lem5317252 c l)). Qed.
Lemma lem5317256 (s : real -> Prop) (c : real) (l : real) : (term352 s c l) = (term350 s c l).
Proof. exact (@lem17362 (term22 s) (term353 c l)). Qed.
Lemma lem5317272 (s : real -> Prop) (c : real) (l : real) : (term352 s c l) = (term351 s c l).
Proof. exact (TRANS (@lem5317256 s c l) (@lem5317255 s c l)). Qed.
Lemma lem5317274 (l : real) (c : real) : (real_lt c l) = (term354 l c).
Proof. exact (@lem1988285 l c). Qed.
Lemma lem5317280 (l : real) (c : real) : (real_sub l c) = (term355 l c).
Proof. exact (@lem1982792 l c). Qed.
Lemma lem5317285 (c : real) (l : real) : (term355 l c) = (term356 c l).
Proof. exact (@lem1982761 (term357 c) l). Qed.
Lemma lem5317287 (c : real) (l : real) : (real_sub l c) = (term356 c l).
Proof. exact (TRANS (@lem5317280 l c) (@lem5317285 c l)). Qed.
Lemma lem5317288 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5317289 (c : real) (l : real) : (term358 l c) = (term359 c l).
Proof. exact (MK_COMB (@lem5317288) (@lem5317287 c l)). Qed.
Lemma lem5317290 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5317291 (c : real) (l : real) : (term354 l c) = (term361 c l).
Proof. exact (MK_COMB (@lem5317289 c l) (@lem5317290)). Qed.
Lemma lem5317292 (c : real) (l : real) : (real_lt c l) = (term361 c l).
Proof. exact (TRANS (@lem5317274 l c) (@lem5317291 c l)). Qed.
Lemma lem5317293 (c : real) (l : real) : (term362 c l) = (term363 c l).
Proof. exact (@lem1988295 (term341 l c) l). Qed.
Lemma lem5317294 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5317296 (x : real) (y : real) : (real_div x y) = (term364 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5317297 (l : real) (c : real) : (term341 l c) = (term365 l c).
Proof. exact (@lem5317296 (real_add l c) term366). Qed.
Lemma lem5317302 (n : nat) : (term367 n) = (term368 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5317304 : term369 = term370.
Proof. exact (@lem5317302 term371). Qed.
Lemma lem5317311 (c : real) (l : real) : (real_add l c) = (real_add c l).
Proof. exact (@lem1982761 c l). Qed.
Lemma lem5317312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317313 (c : real) (l : real) : (term372 l c) = (term372 c l).
Proof. exact (MK_COMB (@lem5317312) (@lem5317311 c l)). Qed.
Lemma lem5317314 (c : real) (l : real) : (term365 l c) = (term373 c l).
Proof. exact (MK_COMB (@lem5317313 c l) (@lem5317304)). Qed.
Lemma lem5317315 (c : real) (l : real) : (term373 c l) = (term374 c l).
Proof. exact (@lem1982725 term370 (real_add c l)). Qed.
Lemma lem5317322 (c : real) (l : real) : (term374 c l) = (term375 c l).
Proof. exact (@lem1982781 c term370 l). Qed.
Lemma lem5317323 (c : real) (l : real) : (term373 c l) = (term375 c l).
Proof. exact (TRANS (@lem5317315 c l) (@lem5317322 c l)). Qed.
Lemma lem5317324 (c : real) (l : real) : (term365 l c) = (term375 c l).
Proof. exact (TRANS (@lem5317314 c l) (@lem5317323 c l)). Qed.
Lemma lem5317325 (c : real) (l : real) : (term341 l c) = (term375 c l).
Proof. exact (TRANS (@lem5317297 l c) (@lem5317324 c l)). Qed.
Lemma lem5317326 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5317327 (c : real) (l : real) : (term376 l c) = (term377 c l).
Proof. exact (MK_COMB (@lem5317326) (@lem5317325 c l)). Qed.
Lemma lem5317328 (c : real) (l : real) : (term378 c l) = (term379 c l).
Proof. exact (MK_COMB (@lem5317327 c l) (@lem5317294 l)). Qed.
Lemma lem5317329 (c : real) (l : real) : (term379 c l) = (term380 c l).
Proof. exact (@lem1982792 (term375 c l) l). Qed.
Lemma lem5317333 (c : real) (l : real) : (term380 c l) = (term381 c l).
Proof. exact (@lem1982755 (term382 c) (term382 l) (term357 l)). Qed.
Lemma lem5317334 (l : real) : (term383 l) = (term384 l).
Proof. exact (@lem1982711 term370 term385 l). Qed.
Lemma lem5317336 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5317337 : term385 = term388.
Proof. exact (@lem5317336 term389). Qed.
Lemma lem5317340 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5317341 : term391 = term392.
Proof. exact (MK_COMB (@lem5317340) (@lem5317337)). Qed.
Lemma lem5317342 : term393.
Proof. exact (@lem1981473 term394 term366 term385 term394 term385 term366). Qed.
Lemma lem5317344 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317345 : term396 = term397.
Proof. exact (@lem5317344 (NUMERAL 0) term371). Qed.
Lemma lem5317346 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317347 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317348 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317347 h1) (fun h1 : term397 = True => @lem5317346)). Qed.
Lemma lem5317349 : term397 = True.
Proof. exact (EQ_MP (@lem5317348) (@lem5317346)). Qed.
Lemma lem5317350 : term396 = True.
Proof. exact (TRANS (@lem5317345) (@lem5317349)). Qed.
Lemma lem5317351 : True = term396.
Proof. exact (SYM (@lem5317350)). Qed.
Lemma lem5317352 : term396.
Proof. exact (EQ_MP (@lem5317351) (@lem0)). Qed.
Lemma lem5317353 : term400.
Proof. exact (@lem5317342 (@lem5317352)). Qed.
Lemma lem5317355 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317356 : term401 = term402.
Proof. exact (@lem5317355 (NUMERAL 0) term389). Qed.
Lemma lem5317357 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317358 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317359 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317358 h1) (fun h1 : term402 = True => @lem5317357)). Qed.
Lemma lem5317360 : term402 = True.
Proof. exact (EQ_MP (@lem5317359) (@lem5317357)). Qed.
Lemma lem5317361 : term401 = True.
Proof. exact (TRANS (@lem5317356) (@lem5317360)). Qed.
Lemma lem5317362 : True = term401.
Proof. exact (SYM (@lem5317361)). Qed.
Lemma lem5317363 : term401.
Proof. exact (EQ_MP (@lem5317362) (@lem0)). Qed.
Lemma lem5317364 : term404.
Proof. exact (@lem5317353 (@lem5317363)). Qed.
Lemma lem5317366 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317367 : term396 = term397.
Proof. exact (@lem5317366 (NUMERAL 0) term371). Qed.
Lemma lem5317368 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317369 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317370 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317369 h1) (fun h1 : term397 = True => @lem5317368)). Qed.
Lemma lem5317371 : term397 = True.
Proof. exact (EQ_MP (@lem5317370) (@lem5317368)). Qed.
Lemma lem5317372 : term396 = True.
Proof. exact (TRANS (@lem5317367) (@lem5317371)). Qed.
Lemma lem5317373 : True = term396.
Proof. exact (SYM (@lem5317372)). Qed.
Lemma lem5317374 : term396.
Proof. exact (EQ_MP (@lem5317373) (@lem0)). Qed.
Lemma lem5317375 : term405.
Proof. exact (@lem5317364 (@lem5317374)). Qed.
Lemma lem5317377 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5317378 : term408 = term409.
Proof. exact (@lem5317377 term389 term371). Qed.
Lemma lem5317379 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317380 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317381 : term411 = term371.
Proof. exact (EQ_MP (@lem5317380) (@lem5317379)). Qed.
Lemma lem5317382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317383 : term412 = term366.
Proof. exact (MK_COMB (@lem5317382) (@lem5317381)). Qed.
Lemma lem5317384 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317385 : term409 = term413.
Proof. exact (MK_COMB (@lem5317384) (@lem5317383)). Qed.
Lemma lem5317386 : term408 = term413.
Proof. exact (TRANS (@lem5317378) (@lem5317385)). Qed.
Lemma lem5317388 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317389 : term416 = term417.
Proof. exact (@lem5317388 term389 term389). Qed.
Lemma lem5317390 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5317391 : term419 = term389.
Proof. exact (EQ_MP (@lem5317390) (@lem940073)). Qed.
Lemma lem5317392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317393 : term417 = term394.
Proof. exact (MK_COMB (@lem5317392) (@lem5317391)). Qed.
Lemma lem5317394 : term416 = term394.
Proof. exact (TRANS (@lem5317389) (@lem5317393)). Qed.
Lemma lem5317395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5317396 : term420 = term421.
Proof. exact (MK_COMB (@lem5317395) (@lem5317394)). Qed.
Lemma lem5317397 : term422 = term423.
Proof. exact (MK_COMB (@lem5317396) (@lem5317386)). Qed.
Lemma lem5317400 : term424 = term385.
Proof. exact (@lem1367771 term389 term389). Qed.
Lemma lem5317401 : term425 = term399.
Proof. exact (@lem706885). Qed.
Lemma lem5317402 : (term425 = term399) = (term426 = term371).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term399). Qed.
Lemma lem5317403 : term426 = term371.
Proof. exact (EQ_MP (@lem5317402) (@lem5317401)). Qed.
Lemma lem5317404 : term371 = term426.
Proof. exact (SYM (@lem5317403)). Qed.
Lemma lem5317405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317406 : term366 = term427.
Proof. exact (MK_COMB (@lem5317405) (@lem5317404)). Qed.
Lemma lem5317407 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317408 : term413 = term428.
Proof. exact (MK_COMB (@lem5317407) (@lem5317406)). Qed.
Lemma lem5317409 : term421 = term421.
Proof. exact (eq_refl term421). Qed.
Lemma lem5317410 : term423 = term424.
Proof. exact (MK_COMB (@lem5317409) (@lem5317408)). Qed.
Lemma lem5317411 : term423 = term385.
Proof. exact (TRANS (@lem5317410) (@lem5317400)). Qed.
Lemma lem5317412 : term422 = term385.
Proof. exact (TRANS (@lem5317397) (@lem5317411)). Qed.
Lemma lem5317413 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317414 : term429 = term430.
Proof. exact (MK_COMB (@lem5317413) (@lem5317412)). Qed.
Lemma lem5317415 : term366 = term366.
Proof. exact (eq_refl term366). Qed.
Lemma lem5317416 : term431 = term408.
Proof. exact (MK_COMB (@lem5317414) (@lem5317415)). Qed.
Lemma lem5317418 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5317419 : term408 = term409.
Proof. exact (@lem5317418 term389 term371). Qed.
Lemma lem5317420 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317421 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317422 : term411 = term371.
Proof. exact (EQ_MP (@lem5317421) (@lem5317420)). Qed.
Lemma lem5317423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317424 : term412 = term366.
Proof. exact (MK_COMB (@lem5317423) (@lem5317422)). Qed.
Lemma lem5317425 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317426 : term409 = term413.
Proof. exact (MK_COMB (@lem5317425) (@lem5317424)). Qed.
Lemma lem5317427 : term408 = term413.
Proof. exact (TRANS (@lem5317419) (@lem5317426)). Qed.
Lemma lem5317428 : term431 = term413.
Proof. exact (TRANS (@lem5317416) (@lem5317427)). Qed.
Lemma lem5317430 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317431 : term432 = term433.
Proof. exact (@lem5317430 term371 term389). Qed.
Lemma lem5317432 : term434 = term399.
Proof. exact (@lem996237 term399). Qed.
Lemma lem5317433 : (term434 = term399) = (term435 = term371).
Proof. exact (@lem1007663 term399 (BIT1 0) term399). Qed.
Lemma lem5317434 : term435 = term371.
Proof. exact (EQ_MP (@lem5317433) (@lem5317432)). Qed.
Lemma lem5317435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317436 : term433 = term366.
Proof. exact (MK_COMB (@lem5317435) (@lem5317434)). Qed.
Lemma lem5317437 : term432 = term366.
Proof. exact (TRANS (@lem5317431) (@lem5317436)). Qed.
Lemma lem5317438 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem5317439 : term436 = term408.
Proof. exact (MK_COMB (@lem5317438) (@lem5317437)). Qed.
Lemma lem5317441 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5317442 : term408 = term409.
Proof. exact (@lem5317441 term389 term371). Qed.
Lemma lem5317443 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317444 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317445 : term411 = term371.
Proof. exact (EQ_MP (@lem5317444) (@lem5317443)). Qed.
Lemma lem5317446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317447 : term412 = term366.
Proof. exact (MK_COMB (@lem5317446) (@lem5317445)). Qed.
Lemma lem5317448 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317449 : term409 = term413.
Proof. exact (MK_COMB (@lem5317448) (@lem5317447)). Qed.
Lemma lem5317450 : term408 = term413.
Proof. exact (TRANS (@lem5317442) (@lem5317449)). Qed.
Lemma lem5317451 : term436 = term413.
Proof. exact (TRANS (@lem5317439) (@lem5317450)). Qed.
Lemma lem5317452 : term413 = term436.
Proof. exact (SYM (@lem5317451)). Qed.
Lemma lem5317453 : term431 = term436.
Proof. exact (TRANS (@lem5317428) (@lem5317452)). Qed.
Lemma lem5317454 : term392 = term437.
Proof. exact (@lem5317375 (@lem5317453)). Qed.
Lemma lem5317457 : term391 = term437.
Proof. exact (TRANS (@lem5317341) (@lem5317454)). Qed.
Lemma lem5317458 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317459 : term438 = term439.
Proof. exact (MK_COMB (@lem5317458) (@lem5317457)). Qed.
Lemma lem5317460 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5317461 (l : real) : (term384 l) = (term440 l).
Proof. exact (MK_COMB (@lem5317459) (@lem5317460 l)). Qed.
Lemma lem5317462 (l : real) : (term383 l) = (term440 l).
Proof. exact (TRANS (@lem5317334 l) (@lem5317461 l)). Qed.
Lemma lem5317463 (c : real) : (term441 c) = (term441 c).
Proof. exact (eq_refl (term441 c)). Qed.
Lemma lem5317464 (c : real) (l : real) : (term381 c l) = (term442 c l).
Proof. exact (MK_COMB (@lem5317463 c) (@lem5317462 l)). Qed.
Lemma lem5317466 (c : real) (l : real) : (term380 c l) = (term442 c l).
Proof. exact (TRANS (@lem5317333 c l) (@lem5317464 c l)). Qed.
Lemma lem5317467 (c : real) (l : real) : (term379 c l) = (term442 c l).
Proof. exact (TRANS (@lem5317329 c l) (@lem5317466 c l)). Qed.
Lemma lem5317468 (c : real) (l : real) : (term378 c l) = (term442 c l).
Proof. exact (TRANS (@lem5317328 c l) (@lem5317467 c l)). Qed.
Lemma lem5317469 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5317470 (c : real) (l : real) : (term443 c l) = (term444 c l).
Proof. exact (MK_COMB (@lem5317469) (@lem5317468 c l)). Qed.
Lemma lem5317471 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5317472 (c : real) (l : real) : (term363 c l) = (term445 c l).
Proof. exact (MK_COMB (@lem5317470 c l) (@lem5317471)). Qed.
Lemma lem5317473 (c : real) (l : real) : (term362 c l) = (term445 c l).
Proof. exact (TRANS (@lem5317293 c l) (@lem5317472 c l)). Qed.
Lemma lem5317474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5317475 (c : real) (l : real) : (term164 c l) = (term446 c l).
Proof. exact (MK_COMB (@lem5317474) (@lem5317292 c l)). Qed.
Lemma lem5317476 (c : real) (l : real) : (term348 c l) = (term447 c l).
Proof. exact (MK_COMB (@lem5317475 c l) (@lem5317473 c l)). Qed.
Lemma lem5317478 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5317479 (s : real -> Prop) (c : real) (l : real) : (term351 s c l) = (term448 s c l).
Proof. exact (MK_COMB (@lem5317478 s) (@lem5317476 c l)). Qed.
Lemma lem5317500 (s : real -> Prop) (c : real) (l : real) : (term352 s c l) = (term448 s c l).
Proof. exact (TRANS (@lem5317272 s c l) (@lem5317479 s c l)). Qed.
Lemma lem5317504 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term448 s c l.
Proof. exact (h1). Qed.
Lemma lem5317505 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term447 c l.
Proof. exact (proj2 (@lem5317504 s c l h1)). Qed.
Lemma lem5317507 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term445 c l.
Proof. exact (proj2 (@lem5317505 s c l h1)). Qed.
Lemma lem5317508 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term361 c l.
Proof. exact (proj1 (@lem5317505 s c l h1)). Qed.
Lemma lem5317510 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5317511 : term449 = term401.
Proof. exact (@lem5317510 term360 term394). Qed.
Lemma lem5317513 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5317514 : term394 = term451.
Proof. exact (@lem5317513 term389). Qed.
Lemma lem5317516 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5317517 : term360 = term452.
Proof. exact (@lem5317516 (NUMERAL 0)). Qed.
Lemma lem5317518 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5317519 : term453 = term454.
Proof. exact (MK_COMB (@lem5317518) (@lem5317517)). Qed.
Lemma lem5317520 : term401 = term455.
Proof. exact (MK_COMB (@lem5317519) (@lem5317514)). Qed.
Lemma lem5317521 : term456.
Proof. exact (@lem1980255 term360 term394 term394 term394). Qed.
Lemma lem5317523 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317524 : term401 = term402.
Proof. exact (@lem5317523 (NUMERAL 0) term389). Qed.
Lemma lem5317525 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317526 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317527 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317526 h1) (fun h1 : term402 = True => @lem5317525)). Qed.
Lemma lem5317528 : term402 = True.
Proof. exact (EQ_MP (@lem5317527) (@lem5317525)). Qed.
Lemma lem5317529 : term401 = True.
Proof. exact (TRANS (@lem5317524) (@lem5317528)). Qed.
Lemma lem5317530 : True = term401.
Proof. exact (SYM (@lem5317529)). Qed.
Lemma lem5317531 : term401.
Proof. exact (EQ_MP (@lem5317530) (@lem0)). Qed.
Lemma lem5317532 : term457.
Proof. exact (@lem5317521 (@lem5317531)). Qed.
Lemma lem5317534 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317535 : term401 = term402.
Proof. exact (@lem5317534 (NUMERAL 0) term389). Qed.
Lemma lem5317536 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317537 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317538 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317537 h1) (fun h1 : term402 = True => @lem5317536)). Qed.
Lemma lem5317539 : term402 = True.
Proof. exact (EQ_MP (@lem5317538) (@lem5317536)). Qed.
Lemma lem5317540 : term401 = True.
Proof. exact (TRANS (@lem5317535) (@lem5317539)). Qed.
Lemma lem5317541 : True = term401.
Proof. exact (SYM (@lem5317540)). Qed.
Lemma lem5317542 : term401.
Proof. exact (EQ_MP (@lem5317541) (@lem0)). Qed.
Lemma lem5317543 : term455 = term458.
Proof. exact (@lem5317532 (@lem5317542)). Qed.
Lemma lem5317545 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317546 : term416 = term417.
Proof. exact (@lem5317545 term389 term389). Qed.
Lemma lem5317547 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5317548 : term419 = term389.
Proof. exact (EQ_MP (@lem5317547) (@lem940073)). Qed.
Lemma lem5317549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317550 : term417 = term394.
Proof. exact (MK_COMB (@lem5317549) (@lem5317548)). Qed.
Lemma lem5317551 : term416 = term394.
Proof. exact (TRANS (@lem5317546) (@lem5317550)). Qed.
Lemma lem5317553 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317554 : term460 = term360.
Proof. exact (@lem5317553 term389). Qed.
Lemma lem5317555 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5317556 : term461 = term453.
Proof. exact (MK_COMB (@lem5317555) (@lem5317554)). Qed.
Lemma lem5317557 : term458 = term401.
Proof. exact (MK_COMB (@lem5317556) (@lem5317551)). Qed.
Lemma lem5317559 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317560 : term401 = term402.
Proof. exact (@lem5317559 (NUMERAL 0) term389). Qed.
Lemma lem5317561 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317562 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317563 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317562 h1) (fun h1 : term402 = True => @lem5317561)). Qed.
Lemma lem5317564 : term402 = True.
Proof. exact (EQ_MP (@lem5317563) (@lem5317561)). Qed.
Lemma lem5317565 : term401 = True.
Proof. exact (TRANS (@lem5317560) (@lem5317564)). Qed.
Lemma lem5317566 : term458 = True.
Proof. exact (TRANS (@lem5317557) (@lem5317565)). Qed.
Lemma lem5317567 : term455 = True.
Proof. exact (TRANS (@lem5317543) (@lem5317566)). Qed.
Lemma lem5317568 : term401 = True.
Proof. exact (TRANS (@lem5317520) (@lem5317567)). Qed.
Lemma lem5317569 : term449 = True.
Proof. exact (TRANS (@lem5317511) (@lem5317568)). Qed.
Lemma lem5317570 : True = term449.
Proof. exact (SYM (@lem5317569)). Qed.
Lemma lem5317571 : term449.
Proof. exact (EQ_MP (@lem5317570) (@lem0)). Qed.
Lemma lem5317572 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term462 c l.
Proof. exact (conj (@lem5317571) (@lem5317507 s c l h1)). Qed.
Lemma lem5317574 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5317575 (c : real) (l : real) : term464 c l.
Proof. exact (@lem5317574 term394 (term442 c l)). Qed.
Lemma lem5317576 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term465 c l.
Proof. exact (@lem5317575 c l (@lem5317572 s c l h1)). Qed.
Lemma lem5317577 (c : real) (l : real) : (term466 c l) = (term442 c l).
Proof. exact (@lem1982733 (term442 c l)). Qed.
Lemma lem5317578 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5317579 (c : real) (l : real) : (term467 c l) = (term444 c l).
Proof. exact (MK_COMB (@lem5317578) (@lem5317577 c l)). Qed.
Lemma lem5317580 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5317581 (c : real) (l : real) : (term465 c l) = (term445 c l).
Proof. exact (MK_COMB (@lem5317579 c l) (@lem5317580)). Qed.
Lemma lem5317582 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term445 c l.
Proof. exact (EQ_MP (@lem5317581 c l) (@lem5317576 s c l h1)). Qed.
Lemma lem5317584 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5317585 : term468 = term469.
Proof. exact (@lem5317584 term360 term370). Qed.
Lemma lem5317586 : term370 = term370.
Proof. exact (eq_refl term370). Qed.
Lemma lem5317588 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5317589 : term360 = term452.
Proof. exact (@lem5317588 (NUMERAL 0)). Qed.
Lemma lem5317590 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5317591 : term453 = term454.
Proof. exact (MK_COMB (@lem5317590) (@lem5317589)). Qed.
Lemma lem5317592 : term469 = term470.
Proof. exact (MK_COMB (@lem5317591) (@lem5317586)). Qed.
Lemma lem5317593 : term471.
Proof. exact (@lem1980255 term360 term366 term394 term394). Qed.
Lemma lem5317595 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317596 : term401 = term402.
Proof. exact (@lem5317595 (NUMERAL 0) term389). Qed.
Lemma lem5317597 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317598 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317599 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317598 h1) (fun h1 : term402 = True => @lem5317597)). Qed.
Lemma lem5317600 : term402 = True.
Proof. exact (EQ_MP (@lem5317599) (@lem5317597)). Qed.
Lemma lem5317601 : term401 = True.
Proof. exact (TRANS (@lem5317596) (@lem5317600)). Qed.
Lemma lem5317602 : True = term401.
Proof. exact (SYM (@lem5317601)). Qed.
Lemma lem5317603 : term401.
Proof. exact (EQ_MP (@lem5317602) (@lem0)). Qed.
Lemma lem5317604 : term472.
Proof. exact (@lem5317593 (@lem5317603)). Qed.
Lemma lem5317606 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317607 : term396 = term397.
Proof. exact (@lem5317606 (NUMERAL 0) term371). Qed.
Lemma lem5317608 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317609 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317610 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317609 h1) (fun h1 : term397 = True => @lem5317608)). Qed.
Lemma lem5317611 : term397 = True.
Proof. exact (EQ_MP (@lem5317610) (@lem5317608)). Qed.
Lemma lem5317612 : term396 = True.
Proof. exact (TRANS (@lem5317607) (@lem5317611)). Qed.
Lemma lem5317613 : True = term396.
Proof. exact (SYM (@lem5317612)). Qed.
Lemma lem5317614 : term396.
Proof. exact (EQ_MP (@lem5317613) (@lem0)). Qed.
Lemma lem5317615 : term470 = term473.
Proof. exact (@lem5317604 (@lem5317614)). Qed.
Lemma lem5317617 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317618 : term416 = term417.
Proof. exact (@lem5317617 term389 term389). Qed.
Lemma lem5317619 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5317620 : term419 = term389.
Proof. exact (EQ_MP (@lem5317619) (@lem940073)). Qed.
Lemma lem5317621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317622 : term417 = term394.
Proof. exact (MK_COMB (@lem5317621) (@lem5317620)). Qed.
Lemma lem5317623 : term416 = term394.
Proof. exact (TRANS (@lem5317618) (@lem5317622)). Qed.
Lemma lem5317625 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317626 : term474 = term360.
Proof. exact (@lem5317625 term371). Qed.
Lemma lem5317627 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5317628 : term475 = term453.
Proof. exact (MK_COMB (@lem5317627) (@lem5317626)). Qed.
Lemma lem5317629 : term473 = term401.
Proof. exact (MK_COMB (@lem5317628) (@lem5317623)). Qed.
Lemma lem5317631 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317632 : term401 = term402.
Proof. exact (@lem5317631 (NUMERAL 0) term389). Qed.
Lemma lem5317633 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317634 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317635 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317634 h1) (fun h1 : term402 = True => @lem5317633)). Qed.
Lemma lem5317636 : term402 = True.
Proof. exact (EQ_MP (@lem5317635) (@lem5317633)). Qed.
Lemma lem5317637 : term401 = True.
Proof. exact (TRANS (@lem5317632) (@lem5317636)). Qed.
Lemma lem5317638 : term473 = True.
Proof. exact (TRANS (@lem5317629) (@lem5317637)). Qed.
Lemma lem5317639 : term470 = True.
Proof. exact (TRANS (@lem5317615) (@lem5317638)). Qed.
Lemma lem5317640 : term469 = True.
Proof. exact (TRANS (@lem5317592) (@lem5317639)). Qed.
Lemma lem5317641 : term468 = True.
Proof. exact (TRANS (@lem5317585) (@lem5317640)). Qed.
Lemma lem5317642 : True = term468.
Proof. exact (SYM (@lem5317641)). Qed.
Lemma lem5317643 : term468.
Proof. exact (EQ_MP (@lem5317642) (@lem0)). Qed.
Lemma lem5317644 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term476 c l.
Proof. exact (conj (@lem5317643) (@lem5317508 s c l h1)). Qed.
Lemma lem5317646 (x : real) (y : real) : term477 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5317647 (c : real) (l : real) : term478 c l.
Proof. exact (@lem5317646 term370 (term356 c l)). Qed.
Lemma lem5317648 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term479 c l.
Proof. exact (@lem5317647 c l (@lem5317644 s c l h1)). Qed.
Lemma lem5317649 (c : real) (l : real) : (term480 c l) = (term481 c l).
Proof. exact (@lem1982781 (term357 c) term370 l). Qed.
Lemma lem5317650 (l : real) : (term382 l) = (term382 l).
Proof. exact (eq_refl (term382 l)). Qed.
Lemma lem5317651 (c : real) : (term482 c) = (term483 c).
Proof. exact (@lem1982749 term370 term385 c). Qed.
Lemma lem5317653 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5317654 : term385 = term388.
Proof. exact (@lem5317653 term389). Qed.
Lemma lem5317657 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem5317658 : term485 = term486.
Proof. exact (MK_COMB (@lem5317657) (@lem5317654)). Qed.
Lemma lem5317659 : term486 = term487.
Proof. exact (@lem1981613 term394 term385 term366 term394). Qed.
Lemma lem5317661 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317662 : term432 = term433.
Proof. exact (@lem5317661 term371 term389). Qed.
Lemma lem5317663 : term434 = term399.
Proof. exact (@lem996237 term399). Qed.
Lemma lem5317664 : (term434 = term399) = (term435 = term371).
Proof. exact (@lem1007663 term399 (BIT1 0) term399). Qed.
Lemma lem5317665 : term435 = term371.
Proof. exact (EQ_MP (@lem5317664) (@lem5317663)). Qed.
Lemma lem5317666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317667 : term433 = term366.
Proof. exact (MK_COMB (@lem5317666) (@lem5317665)). Qed.
Lemma lem5317668 : term432 = term366.
Proof. exact (TRANS (@lem5317662) (@lem5317667)). Qed.
Lemma lem5317670 (m : nat) (n : nat) : (term488 m n) = (term407 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5317671 : term489 = term490.
Proof. exact (@lem5317670 term389 term389). Qed.
Lemma lem5317672 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5317673 : term419 = term389.
Proof. exact (EQ_MP (@lem5317672) (@lem940073)). Qed.
Lemma lem5317674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317675 : term417 = term394.
Proof. exact (MK_COMB (@lem5317674) (@lem5317673)). Qed.
Lemma lem5317676 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317677 : term490 = term385.
Proof. exact (MK_COMB (@lem5317676) (@lem5317675)). Qed.
Lemma lem5317678 : term489 = term385.
Proof. exact (TRANS (@lem5317671) (@lem5317677)). Qed.
Lemma lem5317679 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5317680 : term491 = term492.
Proof. exact (MK_COMB (@lem5317679) (@lem5317678)). Qed.
Lemma lem5317681 : term487 = term437.
Proof. exact (MK_COMB (@lem5317680) (@lem5317668)). Qed.
Lemma lem5317682 : term486 = term437.
Proof. exact (TRANS (@lem5317659) (@lem5317681)). Qed.
Lemma lem5317685 : term485 = term437.
Proof. exact (TRANS (@lem5317658) (@lem5317682)). Qed.
Lemma lem5317686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317687 : term493 = term439.
Proof. exact (MK_COMB (@lem5317686) (@lem5317685)). Qed.
Lemma lem5317688 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5317689 (c : real) : (term483 c) = (term440 c).
Proof. exact (MK_COMB (@lem5317687) (@lem5317688 c)). Qed.
Lemma lem5317690 (c : real) : (term482 c) = (term440 c).
Proof. exact (TRANS (@lem5317651 c) (@lem5317689 c)). Qed.
Lemma lem5317691 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5317692 (c : real) : (term494 c) = (term495 c).
Proof. exact (MK_COMB (@lem5317691) (@lem5317690 c)). Qed.
Lemma lem5317693 (c : real) (l : real) : (term481 c l) = (term496 c l).
Proof. exact (MK_COMB (@lem5317692 c) (@lem5317650 l)). Qed.
Lemma lem5317694 (c : real) (l : real) : (term480 c l) = (term496 c l).
Proof. exact (TRANS (@lem5317649 c l) (@lem5317693 c l)). Qed.
Lemma lem5317695 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5317696 (c : real) (l : real) : (term497 c l) = (term498 c l).
Proof. exact (MK_COMB (@lem5317695) (@lem5317694 c l)). Qed.
Lemma lem5317697 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5317698 (c : real) (l : real) : (term479 c l) = (term499 c l).
Proof. exact (MK_COMB (@lem5317696 c l) (@lem5317697)). Qed.
Lemma lem5317699 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term499 c l.
Proof. exact (EQ_MP (@lem5317698 c l) (@lem5317648 s c l h1)). Qed.
Lemma lem5317700 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term500 c l.
Proof. exact (conj (@lem5317699 s c l h1) (@lem5317582 s c l h1)). Qed.
Lemma lem5317702 (x : real) (y : real) : term501 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5317703 (c : real) (l : real) : term502 c l.
Proof. exact (@lem5317702 (term496 c l) (term442 c l)). Qed.
Lemma lem5317704 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term503 c l.
Proof. exact (@lem5317703 c l (@lem5317700 s c l h1)). Qed.
Lemma lem5317705 (c : real) (l : real) : (term504 c l) = (term505 c l).
Proof. exact (@lem1982753 (term440 c) (term382 c) (term382 l) (term440 l)). Qed.
Lemma lem5317706 (c : real) : (term506 c) = (term507 c).
Proof. exact (@lem1982711 term437 term370 c). Qed.
Lemma lem5317712 : term508.
Proof. exact (@lem1981473 term385 term366 term394 term366 term360 term394). Qed.
Lemma lem5317714 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317715 : term396 = term397.
Proof. exact (@lem5317714 (NUMERAL 0) term371). Qed.
Lemma lem5317716 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317717 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317718 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317717 h1) (fun h1 : term397 = True => @lem5317716)). Qed.
Lemma lem5317719 : term397 = True.
Proof. exact (EQ_MP (@lem5317718) (@lem5317716)). Qed.
Lemma lem5317720 : term396 = True.
Proof. exact (TRANS (@lem5317715) (@lem5317719)). Qed.
Lemma lem5317721 : True = term396.
Proof. exact (SYM (@lem5317720)). Qed.
Lemma lem5317722 : term396.
Proof. exact (EQ_MP (@lem5317721) (@lem0)). Qed.
Lemma lem5317723 : term509.
Proof. exact (@lem5317712 (@lem5317722)). Qed.
Lemma lem5317725 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317726 : term396 = term397.
Proof. exact (@lem5317725 (NUMERAL 0) term371). Qed.
Lemma lem5317727 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317728 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317729 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317728 h1) (fun h1 : term397 = True => @lem5317727)). Qed.
Lemma lem5317730 : term397 = True.
Proof. exact (EQ_MP (@lem5317729) (@lem5317727)). Qed.
Lemma lem5317731 : term396 = True.
Proof. exact (TRANS (@lem5317726) (@lem5317730)). Qed.
Lemma lem5317732 : True = term396.
Proof. exact (SYM (@lem5317731)). Qed.
Lemma lem5317733 : term396.
Proof. exact (EQ_MP (@lem5317732) (@lem0)). Qed.
Lemma lem5317734 : term510.
Proof. exact (@lem5317723 (@lem5317733)). Qed.
Lemma lem5317736 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317737 : term401 = term402.
Proof. exact (@lem5317736 (NUMERAL 0) term389). Qed.
Lemma lem5317738 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317739 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317740 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317739 h1) (fun h1 : term402 = True => @lem5317738)). Qed.
Lemma lem5317741 : term402 = True.
Proof. exact (EQ_MP (@lem5317740) (@lem5317738)). Qed.
Lemma lem5317742 : term401 = True.
Proof. exact (TRANS (@lem5317737) (@lem5317741)). Qed.
Lemma lem5317743 : True = term401.
Proof. exact (SYM (@lem5317742)). Qed.
Lemma lem5317744 : term401.
Proof. exact (EQ_MP (@lem5317743) (@lem0)). Qed.
Lemma lem5317745 : term511.
Proof. exact (@lem5317734 (@lem5317744)). Qed.
Lemma lem5317747 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317748 : term512 = term412.
Proof. exact (@lem5317747 term389 term371). Qed.
Lemma lem5317749 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317750 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317751 : term411 = term371.
Proof. exact (EQ_MP (@lem5317750) (@lem5317749)). Qed.
Lemma lem5317752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317753 : term412 = term366.
Proof. exact (MK_COMB (@lem5317752) (@lem5317751)). Qed.
Lemma lem5317754 : term512 = term366.
Proof. exact (TRANS (@lem5317748) (@lem5317753)). Qed.
Lemma lem5317756 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5317757 : term408 = term409.
Proof. exact (@lem5317756 term389 term371). Qed.
Lemma lem5317758 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317759 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317760 : term411 = term371.
Proof. exact (EQ_MP (@lem5317759) (@lem5317758)). Qed.
Lemma lem5317761 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317762 : term412 = term366.
Proof. exact (MK_COMB (@lem5317761) (@lem5317760)). Qed.
Lemma lem5317763 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317764 : term409 = term413.
Proof. exact (MK_COMB (@lem5317763) (@lem5317762)). Qed.
Lemma lem5317765 : term408 = term413.
Proof. exact (TRANS (@lem5317757) (@lem5317764)). Qed.
Lemma lem5317766 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5317767 : term513 = term514.
Proof. exact (MK_COMB (@lem5317766) (@lem5317765)). Qed.
Lemma lem5317768 : term515 = term516.
Proof. exact (MK_COMB (@lem5317767) (@lem5317754)). Qed.
Lemma lem5317770 (m : nat) : (term517 m) = term360.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5317771 : term516 = term360.
Proof. exact (@lem5317770 term371). Qed.
Lemma lem5317772 : term515 = term360.
Proof. exact (TRANS (@lem5317768) (@lem5317771)). Qed.
Lemma lem5317773 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317774 : term518 = term519.
Proof. exact (MK_COMB (@lem5317773) (@lem5317772)). Qed.
Lemma lem5317775 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem5317776 : term520 = term460.
Proof. exact (MK_COMB (@lem5317774) (@lem5317775)). Qed.
Lemma lem5317778 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317779 : term460 = term360.
Proof. exact (@lem5317778 term389). Qed.
Lemma lem5317780 : term520 = term360.
Proof. exact (TRANS (@lem5317776) (@lem5317779)). Qed.
Lemma lem5317782 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317783 : term521 = term522.
Proof. exact (@lem5317782 term371 term371). Qed.
Lemma lem5317784 : (term418 = (BIT1 0)) = (term523 = term524).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5317785 : term523 = term524.
Proof. exact (EQ_MP (@lem5317784) (@lem940073)). Qed.
Lemma lem5317786 : (term523 = term524) = (term525 = term526).
Proof. exact (@lem1008952 term399 term524). Qed.
Lemma lem5317787 : term525 = term526.
Proof. exact (EQ_MP (@lem5317786) (@lem5317785)). Qed.
Lemma lem5317788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317789 : term522 = term527.
Proof. exact (MK_COMB (@lem5317788) (@lem5317787)). Qed.
Lemma lem5317790 : term521 = term527.
Proof. exact (TRANS (@lem5317783) (@lem5317789)). Qed.
Lemma lem5317791 : term519 = term519.
Proof. exact (eq_refl term519). Qed.
Lemma lem5317792 : term528 = term529.
Proof. exact (MK_COMB (@lem5317791) (@lem5317790)). Qed.
Lemma lem5317794 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317795 : term529 = term360.
Proof. exact (@lem5317794 term526). Qed.
Lemma lem5317796 : term528 = term360.
Proof. exact (TRANS (@lem5317792) (@lem5317795)). Qed.
Lemma lem5317797 : term360 = term528.
Proof. exact (SYM (@lem5317796)). Qed.
Lemma lem5317798 : term520 = term528.
Proof. exact (TRANS (@lem5317780) (@lem5317797)). Qed.
Lemma lem5317800 : term530 = term452.
Proof. exact (@lem5317745 (@lem5317798)). Qed.
Lemma lem5317802 (x : real) : (term531 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5317803 : term452 = term360.
Proof. exact (@lem5317802 term360). Qed.
Lemma lem5317804 : term530 = term360.
Proof. exact (TRANS (@lem5317800) (@lem5317803)). Qed.
Lemma lem5317805 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317806 : term532 = term519.
Proof. exact (MK_COMB (@lem5317805) (@lem5317804)). Qed.
Lemma lem5317807 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5317808 (c : real) : (term507 c) = (term533 c).
Proof. exact (MK_COMB (@lem5317806) (@lem5317807 c)). Qed.
Lemma lem5317809 (c : real) : (term506 c) = (term533 c).
Proof. exact (TRANS (@lem5317706 c) (@lem5317808 c)). Qed.
Lemma lem5317810 (c : real) : (term533 c) = term360.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5317811 (c : real) : (term506 c) = term360.
Proof. exact (TRANS (@lem5317809 c) (@lem5317810 c)). Qed.
Lemma lem5317812 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5317813 (c : real) : (term534 c) = term535.
Proof. exact (MK_COMB (@lem5317812) (@lem5317811 c)). Qed.
Lemma lem5317814 (l : real) : (term536 l) = (term537 l).
Proof. exact (@lem1982711 term370 term437 l). Qed.
Lemma lem5317820 : term538.
Proof. exact (@lem1981473 term394 term366 term385 term366 term360 term394). Qed.
Lemma lem5317822 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317823 : term396 = term397.
Proof. exact (@lem5317822 (NUMERAL 0) term371). Qed.
Lemma lem5317824 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317825 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317826 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317825 h1) (fun h1 : term397 = True => @lem5317824)). Qed.
Lemma lem5317827 : term397 = True.
Proof. exact (EQ_MP (@lem5317826) (@lem5317824)). Qed.
Lemma lem5317828 : term396 = True.
Proof. exact (TRANS (@lem5317823) (@lem5317827)). Qed.
Lemma lem5317829 : True = term396.
Proof. exact (SYM (@lem5317828)). Qed.
Lemma lem5317830 : term396.
Proof. exact (EQ_MP (@lem5317829) (@lem0)). Qed.
Lemma lem5317831 : term539.
Proof. exact (@lem5317820 (@lem5317830)). Qed.
Lemma lem5317833 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317834 : term396 = term397.
Proof. exact (@lem5317833 (NUMERAL 0) term371). Qed.
Lemma lem5317835 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5317836 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5317837 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5317836 h1) (fun h1 : term397 = True => @lem5317835)). Qed.
Lemma lem5317838 : term397 = True.
Proof. exact (EQ_MP (@lem5317837) (@lem5317835)). Qed.
Lemma lem5317839 : term396 = True.
Proof. exact (TRANS (@lem5317834) (@lem5317838)). Qed.
Lemma lem5317840 : True = term396.
Proof. exact (SYM (@lem5317839)). Qed.
Lemma lem5317841 : term396.
Proof. exact (EQ_MP (@lem5317840) (@lem0)). Qed.
Lemma lem5317842 : term540.
Proof. exact (@lem5317831 (@lem5317841)). Qed.
Lemma lem5317844 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317845 : term401 = term402.
Proof. exact (@lem5317844 (NUMERAL 0) term389). Qed.
Lemma lem5317846 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317847 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317848 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317847 h1) (fun h1 : term402 = True => @lem5317846)). Qed.
Lemma lem5317849 : term402 = True.
Proof. exact (EQ_MP (@lem5317848) (@lem5317846)). Qed.
Lemma lem5317850 : term401 = True.
Proof. exact (TRANS (@lem5317845) (@lem5317849)). Qed.
Lemma lem5317851 : True = term401.
Proof. exact (SYM (@lem5317850)). Qed.
Lemma lem5317852 : term401.
Proof. exact (EQ_MP (@lem5317851) (@lem0)). Qed.
Lemma lem5317853 : term541.
Proof. exact (@lem5317842 (@lem5317852)). Qed.
Lemma lem5317855 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5317856 : term408 = term409.
Proof. exact (@lem5317855 term389 term371). Qed.
Lemma lem5317857 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317858 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317859 : term411 = term371.
Proof. exact (EQ_MP (@lem5317858) (@lem5317857)). Qed.
Lemma lem5317860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317861 : term412 = term366.
Proof. exact (MK_COMB (@lem5317860) (@lem5317859)). Qed.
Lemma lem5317862 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5317863 : term409 = term413.
Proof. exact (MK_COMB (@lem5317862) (@lem5317861)). Qed.
Lemma lem5317864 : term408 = term413.
Proof. exact (TRANS (@lem5317856) (@lem5317863)). Qed.
Lemma lem5317866 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317867 : term512 = term412.
Proof. exact (@lem5317866 term389 term371). Qed.
Lemma lem5317868 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5317869 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5317870 : term411 = term371.
Proof. exact (EQ_MP (@lem5317869) (@lem5317868)). Qed.
Lemma lem5317871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317872 : term412 = term366.
Proof. exact (MK_COMB (@lem5317871) (@lem5317870)). Qed.
Lemma lem5317873 : term512 = term366.
Proof. exact (TRANS (@lem5317867) (@lem5317872)). Qed.
Lemma lem5317874 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5317875 : term542 = term543.
Proof. exact (MK_COMB (@lem5317874) (@lem5317873)). Qed.
Lemma lem5317876 : term544 = term545.
Proof. exact (MK_COMB (@lem5317875) (@lem5317864)). Qed.
Lemma lem5317878 (m : nat) : (term546 m) = term360.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5317879 : term545 = term360.
Proof. exact (@lem5317878 term371). Qed.
Lemma lem5317880 : term544 = term360.
Proof. exact (TRANS (@lem5317876) (@lem5317879)). Qed.
Lemma lem5317881 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317882 : term547 = term519.
Proof. exact (MK_COMB (@lem5317881) (@lem5317880)). Qed.
Lemma lem5317883 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem5317884 : term548 = term460.
Proof. exact (MK_COMB (@lem5317882) (@lem5317883)). Qed.
Lemma lem5317886 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317887 : term460 = term360.
Proof. exact (@lem5317886 term389). Qed.
Lemma lem5317888 : term548 = term360.
Proof. exact (TRANS (@lem5317884) (@lem5317887)). Qed.
Lemma lem5317890 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5317891 : term521 = term522.
Proof. exact (@lem5317890 term371 term371). Qed.
Lemma lem5317892 : (term418 = (BIT1 0)) = (term523 = term524).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5317893 : term523 = term524.
Proof. exact (EQ_MP (@lem5317892) (@lem940073)). Qed.
Lemma lem5317894 : (term523 = term524) = (term525 = term526).
Proof. exact (@lem1008952 term399 term524). Qed.
Lemma lem5317895 : term525 = term526.
Proof. exact (EQ_MP (@lem5317894) (@lem5317893)). Qed.
Lemma lem5317896 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5317897 : term522 = term527.
Proof. exact (MK_COMB (@lem5317896) (@lem5317895)). Qed.
Lemma lem5317898 : term521 = term527.
Proof. exact (TRANS (@lem5317891) (@lem5317897)). Qed.
Lemma lem5317899 : term519 = term519.
Proof. exact (eq_refl term519). Qed.
Lemma lem5317900 : term528 = term529.
Proof. exact (MK_COMB (@lem5317899) (@lem5317898)). Qed.
Lemma lem5317902 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317903 : term529 = term360.
Proof. exact (@lem5317902 term526). Qed.
Lemma lem5317904 : term528 = term360.
Proof. exact (TRANS (@lem5317900) (@lem5317903)). Qed.
Lemma lem5317905 : term360 = term528.
Proof. exact (SYM (@lem5317904)). Qed.
Lemma lem5317906 : term548 = term528.
Proof. exact (TRANS (@lem5317888) (@lem5317905)). Qed.
Lemma lem5317908 : term549 = term452.
Proof. exact (@lem5317853 (@lem5317906)). Qed.
Lemma lem5317910 (x : real) : (term531 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5317911 : term452 = term360.
Proof. exact (@lem5317910 term360). Qed.
Lemma lem5317912 : term549 = term360.
Proof. exact (TRANS (@lem5317908) (@lem5317911)). Qed.
Lemma lem5317913 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5317914 : term550 = term519.
Proof. exact (MK_COMB (@lem5317913) (@lem5317912)). Qed.
Lemma lem5317915 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5317916 (l : real) : (term537 l) = (term533 l).
Proof. exact (MK_COMB (@lem5317914) (@lem5317915 l)). Qed.
Lemma lem5317917 (l : real) : (term536 l) = (term533 l).
Proof. exact (TRANS (@lem5317814 l) (@lem5317916 l)). Qed.
Lemma lem5317918 (l : real) : (term533 l) = term360.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5317919 (l : real) : (term536 l) = term360.
Proof. exact (TRANS (@lem5317917 l) (@lem5317918 l)). Qed.
Lemma lem5317920 (c : real) (l : real) : (term505 c l) = term551.
Proof. exact (MK_COMB (@lem5317813 c) (@lem5317919 l)). Qed.
Lemma lem5317921 (c : real) (l : real) : (term504 c l) = term551.
Proof. exact (TRANS (@lem5317705 c l) (@lem5317920 c l)). Qed.
Lemma lem5317922 : term551 = term360.
Proof. exact (@lem1982721 term360). Qed.
Lemma lem5317923 (c : real) (l : real) : (term504 c l) = term360.
Proof. exact (TRANS (@lem5317921 c l) (@lem5317922)). Qed.
Lemma lem5317924 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5317925 (c : real) (l : real) : (term552 c l) = term553.
Proof. exact (MK_COMB (@lem5317924) (@lem5317923 c l)). Qed.
Lemma lem5317926 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5317927 (c : real) (l : real) : (term503 c l) = term554.
Proof. exact (MK_COMB (@lem5317925 c l) (@lem5317926)). Qed.
Lemma lem5317928 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term554.
Proof. exact (EQ_MP (@lem5317927 c l) (@lem5317704 s c l h1)). Qed.
Lemma lem5317930 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5317931 : term554 = term555.
Proof. exact (@lem5317930 term360 term360). Qed.
Lemma lem5317933 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5317934 : term360 = term452.
Proof. exact (@lem5317933 (NUMERAL 0)). Qed.
Lemma lem5317936 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5317937 : term360 = term452.
Proof. exact (@lem5317936 (NUMERAL 0)). Qed.
Lemma lem5317938 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5317939 : term453 = term454.
Proof. exact (MK_COMB (@lem5317938) (@lem5317937)). Qed.
Lemma lem5317940 : term555 = term556.
Proof. exact (MK_COMB (@lem5317939) (@lem5317934)). Qed.
Lemma lem5317941 : term557.
Proof. exact (@lem1980255 term360 term394 term360 term394). Qed.
Lemma lem5317943 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317944 : term401 = term402.
Proof. exact (@lem5317943 (NUMERAL 0) term389). Qed.
Lemma lem5317945 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317946 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317947 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317946 h1) (fun h1 : term402 = True => @lem5317945)). Qed.
Lemma lem5317948 : term402 = True.
Proof. exact (EQ_MP (@lem5317947) (@lem5317945)). Qed.
Lemma lem5317949 : term401 = True.
Proof. exact (TRANS (@lem5317944) (@lem5317948)). Qed.
Lemma lem5317950 : True = term401.
Proof. exact (SYM (@lem5317949)). Qed.
Lemma lem5317951 : term401.
Proof. exact (EQ_MP (@lem5317950) (@lem0)). Qed.
Lemma lem5317952 : term558.
Proof. exact (@lem5317941 (@lem5317951)). Qed.
Lemma lem5317954 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317955 : term401 = term402.
Proof. exact (@lem5317954 (NUMERAL 0) term389). Qed.
Lemma lem5317956 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5317957 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5317958 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5317957 h1) (fun h1 : term402 = True => @lem5317956)). Qed.
Lemma lem5317959 : term402 = True.
Proof. exact (EQ_MP (@lem5317958) (@lem5317956)). Qed.
Lemma lem5317960 : term401 = True.
Proof. exact (TRANS (@lem5317955) (@lem5317959)). Qed.
Lemma lem5317961 : True = term401.
Proof. exact (SYM (@lem5317960)). Qed.
Lemma lem5317962 : term401.
Proof. exact (EQ_MP (@lem5317961) (@lem0)). Qed.
Lemma lem5317963 : term556 = term559.
Proof. exact (@lem5317952 (@lem5317962)). Qed.
Lemma lem5317965 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317966 : term460 = term360.
Proof. exact (@lem5317965 term389). Qed.
Lemma lem5317968 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5317969 : term460 = term360.
Proof. exact (@lem5317968 term389). Qed.
Lemma lem5317970 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5317971 : term461 = term453.
Proof. exact (MK_COMB (@lem5317970) (@lem5317969)). Qed.
Lemma lem5317972 : term559 = term555.
Proof. exact (MK_COMB (@lem5317971) (@lem5317966)). Qed.
Lemma lem5317974 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5317975 : term555 = term560.
Proof. exact (@lem5317974 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5317976 : term560 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5317977 : term555 = False.
Proof. exact (TRANS (@lem5317975) (@lem5317976)). Qed.
Lemma lem5317978 : term559 = False.
Proof. exact (TRANS (@lem5317972) (@lem5317977)). Qed.
Lemma lem5317979 : term556 = False.
Proof. exact (TRANS (@lem5317963) (@lem5317978)). Qed.
Lemma lem5317980 : term555 = False.
Proof. exact (TRANS (@lem5317940) (@lem5317979)). Qed.
Lemma lem5317981 : term554 = False.
Proof. exact (TRANS (@lem5317931) (@lem5317980)). Qed.
Lemma lem5317982 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : False.
Proof. exact (EQ_MP (@lem5317981) (@lem5317928 s c l h1)). Qed.
Lemma lem5317984 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : term448 s c l.
Proof. exact (h1). Qed.
Lemma lem5317985 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : (term448 s c l) = False.
Proof. exact (prop_ext (fun h2 : term448 s c l => @lem5317982 s c l h1) (fun h2 : False => @lem5317984 s c l h1)). Qed.
Lemma lem5317986 (s : real -> Prop) (c : real) (l : real) (h1 : term448 s c l) : False.
Proof. exact (EQ_MP (@lem5317985 s c l h1) (@lem5317984 s c l h1)). Qed.
Lemma lem5317987 (s : real -> Prop) (c : real) (l : real) (h1 : term352 s c l) : term352 s c l.
Proof. exact (h1). Qed.
Lemma lem5317988 (s : real -> Prop) (c : real) (l : real) (h1 : term352 s c l) : term448 s c l.
Proof. exact (EQ_MP (@lem5317500 s c l) (@lem5317987 s c l h1)). Qed.
Lemma lem5317989 (s : real -> Prop) (c : real) (l : real) (h1 : term352 s c l) : (term448 s c l) = False.
Proof. exact (prop_ext (fun h2 : term448 s c l => @lem5317986 s c l h2) (fun h2 : False => @lem5317988 s c l h1)). Qed.
Lemma lem5317990 (s : real -> Prop) (c : real) (l : real) (h1 : term352 s c l) : False.
Proof. exact (EQ_MP (@lem5317989 s c l h1) (@lem5317988 s c l h1)). Qed.
Lemma lem5317991 (s : real -> Prop) (c : real) (l : real) : term561 s c l.
Proof. exact (fun h0 : term352 s c l => @lem5317990 s c l h0). Qed.
Lemma lem5317992 (s : real -> Prop) (c : real) (l : real) : term562 s c l.
Proof. exact (@lem1386578 (term563 s c l)). Qed.
Lemma lem5317995 (s : real -> Prop) (c : real) (l : real) : term563 s c l.
Proof. exact (@lem5317992 s c l (@lem5317991 s c l)). Qed.
Lemma lem5317996 (c : real) (l : real) (s : real -> Prop) (h1 : term22 s) : term353 c l.
Proof. exact (@lem5317995 s c l (@lem5317177 s h1)). Qed.
Lemma lem5317997 (s : real -> Prop) (c : real) (l : real) (h1 : term22 s) (h2 : real_lt c l) : term345 c l.
Proof. exact (@lem5317996 c l s h1 (@lem5317230 c l h2)). Qed.
Lemma lem5317998 (s : real -> Prop) (l : real) (c : real) (h1 : term346 s l c) : term346 s l c.
Proof. exact (h1). Qed.
Lemma lem5317999 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term564 s l c x0) : term564 s l c x0.
Proof. exact (h1). Qed.
Lemma lem5318000 (l : real) (c : real) (x0 : real) (h1 : term565 l c x0) : term565 l c x0.
Proof. exact (h1). Qed.
Lemma lem5318001 (x0 : real) (s : real -> Prop) (h1 : @IN real x0 s) : @IN real x0 s.
Proof. exact (h1). Qed.
Lemma lem5318002 (x : real) (s : real -> Prop) (c : real) (h1 : term25 s c) : term61 s c x.
Proof. exact (@lem5317225 s c h1 x). Qed.
Lemma lem5318003 (s : real -> Prop) (x : real) (c : real) : (term61 s c x) = (term54 s x c).
Proof. exact (eq_refl (term61 s c x)). Qed.
Lemma lem5318006 (x : real) (s : real -> Prop) (c : real) (h1 : term25 s c) : term54 s x c.
Proof. exact (EQ_MP (@lem5318003 s x c) (@lem5318002 x s c h1)). Qed.
Lemma lem5318007 (x0 : real) (s : real -> Prop) (c : real) (h1 : term25 s c) : term54 s x0 c.
Proof. exact (@lem5318006 x0 s c h1). Qed.
Lemma lem5318008 (c : real) (x0 : real) (s : real -> Prop) (h1 : term25 s c) (h2 : @IN real x0 s) : real_le x0 c.
Proof. exact (@lem5318007 x0 s c h1 (@lem5318001 x0 s h2)). Qed.
Lemma lem5318020 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5318021 (l : real) (c : real) (x0 : real) : (term566 l c x0) = (term567 l c x0).
Proof. exact (@lem5318020 (term565 l c x0)). Qed.
Lemma lem5318022 (x0 : real) (c : real) : (term568 x0 c) = (term568 x0 c).
Proof. exact (eq_refl (term568 x0 c)). Qed.
Lemma lem5318023 (l : real) (c : real) (x0 : real) : (term569 l c x0) = (term570 l c x0).
Proof. exact (MK_COMB (@lem5318022 x0 c) (@lem5318021 l c x0)). Qed.
Lemma lem5318026 (x0 : real) (s : real -> Prop) : (term571 x0 s) = (term571 x0 s).
Proof. exact (eq_refl (term571 x0 s)). Qed.
Lemma lem5318027 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term572 s l c x0) = (term573 s l c x0).
Proof. exact (MK_COMB (@lem5318026 x0 s) (@lem5318023 l c x0)). Qed.
Lemma lem5318030 (c : real) (l : real) : (term150 c l) = (term150 c l).
Proof. exact (eq_refl (term150 c l)). Qed.
Lemma lem5318031 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term574 s l c x0) = (term575 s l c x0).
Proof. exact (MK_COMB (@lem5318030 c l) (@lem5318027 s l c x0)). Qed.
Lemma lem5318034 (s : real -> Prop) : (term576 s) = (term576 s).
Proof. exact (eq_refl (term576 s)). Qed.
Lemma lem5318035 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term577 s l c x0) = (term578 s l c x0).
Proof. exact (MK_COMB (@lem5318034 s) (@lem5318031 s l c x0)). Qed.
Lemma lem5318038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5318040 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term579 s l c x0) = (term580 s l c x0).
Proof. exact (MK_COMB (@lem5318038) (@lem5318035 s l c x0)). Qed.
Lemma lem5318047 (l : real) (c : real) (x0 : real) : (term581 l c x0) = (term565 l c x0).
Proof. exact (@lem16933 (term565 l c x0)). Qed.
Lemma lem5318049 (x0 : real) (c : real) : (term582 x0 c) = (term582 x0 c).
Proof. exact (eq_refl (term582 x0 c)). Qed.
Lemma lem5318050 (l : real) (c : real) (x0 : real) : (term583 l c x0) = (term584 l c x0).
Proof. exact (MK_COMB (@lem5318049 x0 c) (@lem5318047 l c x0)). Qed.
Lemma lem5318051 (l : real) (c : real) (x0 : real) : (term585 l c x0) = (term583 l c x0).
Proof. exact (@lem17362 (real_le x0 c) (term567 l c x0)). Qed.
Lemma lem5318052 (l : real) (c : real) (x0 : real) : (term585 l c x0) = (term584 l c x0).
Proof. exact (TRANS (@lem5318051 l c x0) (@lem5318050 l c x0)). Qed.
Lemma lem5318054 (x0 : real) (s : real -> Prop) : (term586 x0 s) = (term586 x0 s).
Proof. exact (eq_refl (term586 x0 s)). Qed.
Lemma lem5318055 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term587 s l c x0) = (term588 s l c x0).
Proof. exact (MK_COMB (@lem5318054 x0 s) (@lem5318052 l c x0)). Qed.
Lemma lem5318056 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term589 s l c x0) = (term587 s l c x0).
Proof. exact (@lem17362 (@IN real x0 s) (term570 l c x0)). Qed.
Lemma lem5318057 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term589 s l c x0) = (term588 s l c x0).
Proof. exact (TRANS (@lem5318056 s l c x0) (@lem5318055 s l c x0)). Qed.
Lemma lem5318059 (c : real) (l : real) : (term164 c l) = (term164 c l).
Proof. exact (eq_refl (term164 c l)). Qed.
Lemma lem5318060 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term590 s l c x0) = (term591 s l c x0).
Proof. exact (MK_COMB (@lem5318059 c l) (@lem5318057 s l c x0)). Qed.
Lemma lem5318061 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term592 s l c x0) = (term590 s l c x0).
Proof. exact (@lem17362 (real_lt c l) (term573 s l c x0)). Qed.
Lemma lem5318062 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term592 s l c x0) = (term591 s l c x0).
Proof. exact (TRANS (@lem5318061 s l c x0) (@lem5318060 s l c x0)). Qed.
Lemma lem5318064 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5318065 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term593 s l c x0) = (term594 s l c x0).
Proof. exact (MK_COMB (@lem5318064 s) (@lem5318062 s l c x0)). Qed.
Lemma lem5318066 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term580 s l c x0) = (term593 s l c x0).
Proof. exact (@lem17362 (term22 s) (term575 s l c x0)). Qed.
Lemma lem5318067 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term580 s l c x0) = (term594 s l c x0).
Proof. exact (TRANS (@lem5318066 s l c x0) (@lem5318065 s l c x0)). Qed.
Lemma lem5318088 (s : real -> Prop) (l : real) (c : real) (x0 : real) : (term579 s l c x0) = (term594 s l c x0).
Proof. exact (TRANS (@lem5318040 s l c x0) (@lem5318067 s l c x0)). Qed.
Lemma lem5318090 (l : real) (c : real) : (real_lt c l) = (term354 l c).
Proof. exact (@lem1988285 l c). Qed.
Lemma lem5318096 (l : real) (c : real) : (real_sub l c) = (term355 l c).
Proof. exact (@lem1982792 l c). Qed.
Lemma lem5318101 (c : real) (l : real) : (term355 l c) = (term356 c l).
Proof. exact (@lem1982761 (term357 c) l). Qed.
Lemma lem5318103 (c : real) (l : real) : (real_sub l c) = (term356 c l).
Proof. exact (TRANS (@lem5318096 l c) (@lem5318101 c l)). Qed.
Lemma lem5318104 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5318105 (c : real) (l : real) : (term358 l c) = (term359 c l).
Proof. exact (MK_COMB (@lem5318104) (@lem5318103 c l)). Qed.
Lemma lem5318106 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318107 (c : real) (l : real) : (term354 l c) = (term361 c l).
Proof. exact (MK_COMB (@lem5318105 c l) (@lem5318106)). Qed.
Lemma lem5318108 (c : real) (l : real) : (real_lt c l) = (term361 c l).
Proof. exact (TRANS (@lem5318090 l c) (@lem5318107 c l)). Qed.
Lemma lem5318110 (c : real) (x0 : real) : (real_le x0 c) = (term595 c x0).
Proof. exact (@lem1988287 c x0). Qed.
Lemma lem5318123 (c : real) (x0 : real) : (real_sub c x0) = (term355 c x0).
Proof. exact (@lem1982792 c x0). Qed.
Lemma lem5318124 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5318125 (c : real) (x0 : real) : (term596 c x0) = (term597 c x0).
Proof. exact (MK_COMB (@lem5318124) (@lem5318123 c x0)). Qed.
Lemma lem5318126 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318127 (c : real) (x0 : real) : (term595 c x0) = (term598 c x0).
Proof. exact (MK_COMB (@lem5318125 c x0) (@lem5318126)). Qed.
Lemma lem5318128 (c : real) (x0 : real) : (real_le x0 c) = (term598 c x0).
Proof. exact (TRANS (@lem5318110 c x0) (@lem5318127 c x0)). Qed.
Lemma lem5318129 (x0 : real) (l : real) (c : real) : (term565 l c x0) = (term599 x0 l c).
Proof. exact (@lem1988285 x0 (term341 l c)). Qed.
Lemma lem5318131 (x : real) (y : real) : (real_div x y) = (term364 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5318132 (l : real) (c : real) : (term341 l c) = (term365 l c).
Proof. exact (@lem5318131 (real_add l c) term366). Qed.
Lemma lem5318137 (n : nat) : (term367 n) = (term368 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5318139 : term369 = term370.
Proof. exact (@lem5318137 term371). Qed.
Lemma lem5318146 (c : real) (l : real) : (real_add l c) = (real_add c l).
Proof. exact (@lem1982761 c l). Qed.
Lemma lem5318147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318148 (c : real) (l : real) : (term372 l c) = (term372 c l).
Proof. exact (MK_COMB (@lem5318147) (@lem5318146 c l)). Qed.
Lemma lem5318149 (c : real) (l : real) : (term365 l c) = (term373 c l).
Proof. exact (MK_COMB (@lem5318148 c l) (@lem5318139)). Qed.
Lemma lem5318150 (c : real) (l : real) : (term373 c l) = (term374 c l).
Proof. exact (@lem1982725 term370 (real_add c l)). Qed.
Lemma lem5318157 (c : real) (l : real) : (term374 c l) = (term375 c l).
Proof. exact (@lem1982781 c term370 l). Qed.
Lemma lem5318158 (c : real) (l : real) : (term373 c l) = (term375 c l).
Proof. exact (TRANS (@lem5318150 c l) (@lem5318157 c l)). Qed.
Lemma lem5318159 (c : real) (l : real) : (term365 l c) = (term375 c l).
Proof. exact (TRANS (@lem5318149 c l) (@lem5318158 c l)). Qed.
Lemma lem5318160 (c : real) (l : real) : (term341 l c) = (term375 c l).
Proof. exact (TRANS (@lem5318132 l c) (@lem5318159 c l)). Qed.
Lemma lem5318163 (x0 : real) : (real_sub x0) = (real_sub x0).
Proof. exact (eq_refl (real_sub x0)). Qed.
Lemma lem5318164 (x0 : real) (c : real) (l : real) : (term600 x0 l c) = (term601 x0 c l).
Proof. exact (MK_COMB (@lem5318163 x0) (@lem5318160 c l)). Qed.
Lemma lem5318165 (x0 : real) (c : real) (l : real) : (term601 x0 c l) = (term602 x0 c l).
Proof. exact (@lem1982792 x0 (term375 c l)). Qed.
Lemma lem5318166 (c : real) (l : real) : (term603 c l) = (term604 c l).
Proof. exact (@lem1982781 (term382 c) term385 (term382 l)). Qed.
Lemma lem5318167 (l : real) : (term605 l) = (term606 l).
Proof. exact (@lem1982749 term385 term370 l). Qed.
Lemma lem5318168 : term370 = term370.
Proof. exact (eq_refl term370). Qed.
Lemma lem5318170 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5318171 : term385 = term388.
Proof. exact (@lem5318170 term389). Qed.
Lemma lem5318172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318173 : term430 = term607.
Proof. exact (MK_COMB (@lem5318172) (@lem5318171)). Qed.
Lemma lem5318174 : term608 = term609.
Proof. exact (MK_COMB (@lem5318173) (@lem5318168)). Qed.
Lemma lem5318175 : term609 = term610.
Proof. exact (@lem1981613 term385 term394 term394 term366). Qed.
Lemma lem5318177 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318178 : term512 = term412.
Proof. exact (@lem5318177 term389 term371). Qed.
Lemma lem5318179 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5318180 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5318181 : term411 = term371.
Proof. exact (EQ_MP (@lem5318180) (@lem5318179)). Qed.
Lemma lem5318182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318183 : term412 = term366.
Proof. exact (MK_COMB (@lem5318182) (@lem5318181)). Qed.
Lemma lem5318184 : term512 = term366.
Proof. exact (TRANS (@lem5318178) (@lem5318183)). Qed.
Lemma lem5318186 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318187 : term611 = term490.
Proof. exact (@lem5318186 term389 term389). Qed.
Lemma lem5318188 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318189 : term419 = term389.
Proof. exact (EQ_MP (@lem5318188) (@lem940073)). Qed.
Lemma lem5318190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318191 : term417 = term394.
Proof. exact (MK_COMB (@lem5318190) (@lem5318189)). Qed.
Lemma lem5318192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318193 : term490 = term385.
Proof. exact (MK_COMB (@lem5318192) (@lem5318191)). Qed.
Lemma lem5318194 : term611 = term385.
Proof. exact (TRANS (@lem5318187) (@lem5318193)). Qed.
Lemma lem5318195 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5318196 : term612 = term492.
Proof. exact (MK_COMB (@lem5318195) (@lem5318194)). Qed.
Lemma lem5318197 : term610 = term437.
Proof. exact (MK_COMB (@lem5318196) (@lem5318184)). Qed.
Lemma lem5318198 : term609 = term437.
Proof. exact (TRANS (@lem5318175) (@lem5318197)). Qed.
Lemma lem5318201 : term608 = term437.
Proof. exact (TRANS (@lem5318174) (@lem5318198)). Qed.
Lemma lem5318202 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318203 : term613 = term439.
Proof. exact (MK_COMB (@lem5318202) (@lem5318201)). Qed.
Lemma lem5318204 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5318205 (l : real) : (term606 l) = (term440 l).
Proof. exact (MK_COMB (@lem5318203) (@lem5318204 l)). Qed.
Lemma lem5318206 (l : real) : (term605 l) = (term440 l).
Proof. exact (TRANS (@lem5318167 l) (@lem5318205 l)). Qed.
Lemma lem5318207 (c : real) : (term605 c) = (term606 c).
Proof. exact (@lem1982749 term385 term370 c). Qed.
Lemma lem5318208 : term370 = term370.
Proof. exact (eq_refl term370). Qed.
Lemma lem5318210 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5318211 : term385 = term388.
Proof. exact (@lem5318210 term389). Qed.
Lemma lem5318212 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318213 : term430 = term607.
Proof. exact (MK_COMB (@lem5318212) (@lem5318211)). Qed.
Lemma lem5318214 : term608 = term609.
Proof. exact (MK_COMB (@lem5318213) (@lem5318208)). Qed.
Lemma lem5318215 : term609 = term610.
Proof. exact (@lem1981613 term385 term394 term394 term366). Qed.
Lemma lem5318217 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318218 : term512 = term412.
Proof. exact (@lem5318217 term389 term371). Qed.
Lemma lem5318219 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5318220 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5318221 : term411 = term371.
Proof. exact (EQ_MP (@lem5318220) (@lem5318219)). Qed.
Lemma lem5318222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318223 : term412 = term366.
Proof. exact (MK_COMB (@lem5318222) (@lem5318221)). Qed.
Lemma lem5318224 : term512 = term366.
Proof. exact (TRANS (@lem5318218) (@lem5318223)). Qed.
Lemma lem5318226 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318227 : term611 = term490.
Proof. exact (@lem5318226 term389 term389). Qed.
Lemma lem5318228 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318229 : term419 = term389.
Proof. exact (EQ_MP (@lem5318228) (@lem940073)). Qed.
Lemma lem5318230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318231 : term417 = term394.
Proof. exact (MK_COMB (@lem5318230) (@lem5318229)). Qed.
Lemma lem5318232 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318233 : term490 = term385.
Proof. exact (MK_COMB (@lem5318232) (@lem5318231)). Qed.
Lemma lem5318234 : term611 = term385.
Proof. exact (TRANS (@lem5318227) (@lem5318233)). Qed.
Lemma lem5318235 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5318236 : term612 = term492.
Proof. exact (MK_COMB (@lem5318235) (@lem5318234)). Qed.
Lemma lem5318237 : term610 = term437.
Proof. exact (MK_COMB (@lem5318236) (@lem5318224)). Qed.
Lemma lem5318238 : term609 = term437.
Proof. exact (TRANS (@lem5318215) (@lem5318237)). Qed.
Lemma lem5318241 : term608 = term437.
Proof. exact (TRANS (@lem5318214) (@lem5318238)). Qed.
Lemma lem5318242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318243 : term613 = term439.
Proof. exact (MK_COMB (@lem5318242) (@lem5318241)). Qed.
Lemma lem5318244 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5318245 (c : real) : (term606 c) = (term440 c).
Proof. exact (MK_COMB (@lem5318243) (@lem5318244 c)). Qed.
Lemma lem5318246 (c : real) : (term605 c) = (term440 c).
Proof. exact (TRANS (@lem5318207 c) (@lem5318245 c)). Qed.
Lemma lem5318247 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318248 (c : real) : (term614 c) = (term495 c).
Proof. exact (MK_COMB (@lem5318247) (@lem5318246 c)). Qed.
Lemma lem5318249 (c : real) (l : real) : (term604 c l) = (term615 c l).
Proof. exact (MK_COMB (@lem5318248 c) (@lem5318206 l)). Qed.
Lemma lem5318250 (c : real) (l : real) : (term603 c l) = (term615 c l).
Proof. exact (TRANS (@lem5318166 c l) (@lem5318249 c l)). Qed.
Lemma lem5318251 (x0 : real) : (real_add x0) = (real_add x0).
Proof. exact (eq_refl (real_add x0)). Qed.
Lemma lem5318252 (x0 : real) (c : real) (l : real) : (term602 x0 c l) = (term616 x0 c l).
Proof. exact (MK_COMB (@lem5318251 x0) (@lem5318250 c l)). Qed.
Lemma lem5318253 (c : real) (x0 : real) (l : real) : (term616 x0 c l) = (term617 c x0 l).
Proof. exact (@lem1982757 (term440 c) x0 (term440 l)). Qed.
Lemma lem5318254 (l : real) (x0 : real) : (term618 x0 l) = (term619 l x0).
Proof. exact (@lem1982761 (term440 l) x0). Qed.
Lemma lem5318255 (c : real) : (term495 c) = (term495 c).
Proof. exact (eq_refl (term495 c)). Qed.
Lemma lem5318256 (c : real) (l : real) (x0 : real) : (term617 c x0 l) = (term620 c l x0).
Proof. exact (MK_COMB (@lem5318255 c) (@lem5318254 l x0)). Qed.
Lemma lem5318257 (c : real) (l : real) (x0 : real) : (term616 x0 c l) = (term620 c l x0).
Proof. exact (TRANS (@lem5318253 c x0 l) (@lem5318256 c l x0)). Qed.
Lemma lem5318258 (c : real) (l : real) (x0 : real) : (term602 x0 c l) = (term620 c l x0).
Proof. exact (TRANS (@lem5318252 x0 c l) (@lem5318257 c l x0)). Qed.
Lemma lem5318259 (c : real) (l : real) (x0 : real) : (term601 x0 c l) = (term620 c l x0).
Proof. exact (TRANS (@lem5318165 x0 c l) (@lem5318258 c l x0)). Qed.
Lemma lem5318260 (c : real) (l : real) (x0 : real) : (term600 x0 l c) = (term620 c l x0).
Proof. exact (TRANS (@lem5318164 x0 c l) (@lem5318259 c l x0)). Qed.
Lemma lem5318261 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5318262 (c : real) (l : real) (x0 : real) : (term621 x0 l c) = (term622 c l x0).
Proof. exact (MK_COMB (@lem5318261) (@lem5318260 c l x0)). Qed.
Lemma lem5318263 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318264 (c : real) (l : real) (x0 : real) : (term599 x0 l c) = (term623 c l x0).
Proof. exact (MK_COMB (@lem5318262 c l x0) (@lem5318263)). Qed.
Lemma lem5318265 (c : real) (l : real) (x0 : real) : (term565 l c x0) = (term623 c l x0).
Proof. exact (TRANS (@lem5318129 x0 l c) (@lem5318264 c l x0)). Qed.
Lemma lem5318266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5318267 (c : real) (x0 : real) : (term582 x0 c) = (term624 c x0).
Proof. exact (MK_COMB (@lem5318266) (@lem5318128 c x0)). Qed.
Lemma lem5318268 (c : real) (l : real) (x0 : real) : (term584 l c x0) = (term625 c l x0).
Proof. exact (MK_COMB (@lem5318267 c x0) (@lem5318265 c l x0)). Qed.
Lemma lem5318270 (x0 : real) (s : real -> Prop) : (term586 x0 s) = (term586 x0 s).
Proof. exact (eq_refl (term586 x0 s)). Qed.
Lemma lem5318271 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term588 s l c x0) = (term626 s c l x0).
Proof. exact (MK_COMB (@lem5318270 x0 s) (@lem5318268 c l x0)). Qed.
Lemma lem5318272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5318273 (c : real) (l : real) : (term164 c l) = (term446 c l).
Proof. exact (MK_COMB (@lem5318272) (@lem5318108 c l)). Qed.
Lemma lem5318274 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term591 s l c x0) = (term627 s c l x0).
Proof. exact (MK_COMB (@lem5318273 c l) (@lem5318271 s c l x0)). Qed.
Lemma lem5318276 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (eq_refl (term349 s)). Qed.
Lemma lem5318277 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term594 s l c x0) = (term628 s c l x0).
Proof. exact (MK_COMB (@lem5318276 s) (@lem5318274 s c l x0)). Qed.
Lemma lem5318310 (s : real -> Prop) (c : real) (l : real) (x0 : real) : (term579 s l c x0) = (term628 s c l x0).
Proof. exact (TRANS (@lem5318088 s l c x0) (@lem5318277 s c l x0)). Qed.
Lemma lem5318314 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term628 s c l x0.
Proof. exact (h1). Qed.
Lemma lem5318315 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term627 s c l x0.
Proof. exact (proj2 (@lem5318314 s c l x0 h1)). Qed.
Lemma lem5318317 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term626 s c l x0.
Proof. exact (proj2 (@lem5318315 s c l x0 h1)). Qed.
Lemma lem5318318 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term361 c l.
Proof. exact (proj1 (@lem5318315 s c l x0 h1)). Qed.
Lemma lem5318319 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term625 c l x0.
Proof. exact (proj2 (@lem5318317 s c l x0 h1)). Qed.
Lemma lem5318321 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term623 c l x0.
Proof. exact (proj2 (@lem5318319 s c l x0 h1)). Qed.
Lemma lem5318322 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term598 c x0.
Proof. exact (proj1 (@lem5318319 s c l x0 h1)). Qed.
Lemma lem5318324 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5318325 : term449 = term401.
Proof. exact (@lem5318324 term360 term394). Qed.
Lemma lem5318327 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318328 : term394 = term451.
Proof. exact (@lem5318327 term389). Qed.
Lemma lem5318330 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318331 : term360 = term452.
Proof. exact (@lem5318330 (NUMERAL 0)). Qed.
Lemma lem5318332 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318333 : term453 = term454.
Proof. exact (MK_COMB (@lem5318332) (@lem5318331)). Qed.
Lemma lem5318334 : term401 = term455.
Proof. exact (MK_COMB (@lem5318333) (@lem5318328)). Qed.
Lemma lem5318335 : term456.
Proof. exact (@lem1980255 term360 term394 term394 term394). Qed.
Lemma lem5318337 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318338 : term401 = term402.
Proof. exact (@lem5318337 (NUMERAL 0) term389). Qed.
Lemma lem5318339 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318340 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318341 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318340 h1) (fun h1 : term402 = True => @lem5318339)). Qed.
Lemma lem5318342 : term402 = True.
Proof. exact (EQ_MP (@lem5318341) (@lem5318339)). Qed.
Lemma lem5318343 : term401 = True.
Proof. exact (TRANS (@lem5318338) (@lem5318342)). Qed.
Lemma lem5318344 : True = term401.
Proof. exact (SYM (@lem5318343)). Qed.
Lemma lem5318345 : term401.
Proof. exact (EQ_MP (@lem5318344) (@lem0)). Qed.
Lemma lem5318346 : term457.
Proof. exact (@lem5318335 (@lem5318345)). Qed.
Lemma lem5318348 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318349 : term401 = term402.
Proof. exact (@lem5318348 (NUMERAL 0) term389). Qed.
Lemma lem5318350 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318351 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318352 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318351 h1) (fun h1 : term402 = True => @lem5318350)). Qed.
Lemma lem5318353 : term402 = True.
Proof. exact (EQ_MP (@lem5318352) (@lem5318350)). Qed.
Lemma lem5318354 : term401 = True.
Proof. exact (TRANS (@lem5318349) (@lem5318353)). Qed.
Lemma lem5318355 : True = term401.
Proof. exact (SYM (@lem5318354)). Qed.
Lemma lem5318356 : term401.
Proof. exact (EQ_MP (@lem5318355) (@lem0)). Qed.
Lemma lem5318357 : term455 = term458.
Proof. exact (@lem5318346 (@lem5318356)). Qed.
Lemma lem5318359 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318360 : term416 = term417.
Proof. exact (@lem5318359 term389 term389). Qed.
Lemma lem5318361 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318362 : term419 = term389.
Proof. exact (EQ_MP (@lem5318361) (@lem940073)). Qed.
Lemma lem5318363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318364 : term417 = term394.
Proof. exact (MK_COMB (@lem5318363) (@lem5318362)). Qed.
Lemma lem5318365 : term416 = term394.
Proof. exact (TRANS (@lem5318360) (@lem5318364)). Qed.
Lemma lem5318367 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5318368 : term460 = term360.
Proof. exact (@lem5318367 term389). Qed.
Lemma lem5318369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318370 : term461 = term453.
Proof. exact (MK_COMB (@lem5318369) (@lem5318368)). Qed.
Lemma lem5318371 : term458 = term401.
Proof. exact (MK_COMB (@lem5318370) (@lem5318365)). Qed.
Lemma lem5318373 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318374 : term401 = term402.
Proof. exact (@lem5318373 (NUMERAL 0) term389). Qed.
Lemma lem5318375 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318376 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318377 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318376 h1) (fun h1 : term402 = True => @lem5318375)). Qed.
Lemma lem5318378 : term402 = True.
Proof. exact (EQ_MP (@lem5318377) (@lem5318375)). Qed.
Lemma lem5318379 : term401 = True.
Proof. exact (TRANS (@lem5318374) (@lem5318378)). Qed.
Lemma lem5318380 : term458 = True.
Proof. exact (TRANS (@lem5318371) (@lem5318379)). Qed.
Lemma lem5318381 : term455 = True.
Proof. exact (TRANS (@lem5318357) (@lem5318380)). Qed.
Lemma lem5318382 : term401 = True.
Proof. exact (TRANS (@lem5318334) (@lem5318381)). Qed.
Lemma lem5318383 : term449 = True.
Proof. exact (TRANS (@lem5318325) (@lem5318382)). Qed.
Lemma lem5318384 : True = term449.
Proof. exact (SYM (@lem5318383)). Qed.
Lemma lem5318385 : term449.
Proof. exact (EQ_MP (@lem5318384) (@lem0)). Qed.
Lemma lem5318386 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term629 c x0.
Proof. exact (conj (@lem5318385) (@lem5318322 s c l x0 h1)). Qed.
Lemma lem5318388 (x : real) (y : real) : term463 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5318389 (c : real) (x0 : real) : term630 c x0.
Proof. exact (@lem5318388 term394 (term355 c x0)). Qed.
Lemma lem5318390 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term631 c x0.
Proof. exact (@lem5318389 c x0 (@lem5318386 s c l x0 h1)). Qed.
Lemma lem5318391 (c : real) (x0 : real) : (term632 c x0) = (term355 c x0).
Proof. exact (@lem1982733 (term355 c x0)). Qed.
Lemma lem5318392 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5318393 (c : real) (x0 : real) : (term633 c x0) = (term597 c x0).
Proof. exact (MK_COMB (@lem5318392) (@lem5318391 c x0)). Qed.
Lemma lem5318394 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318395 (c : real) (x0 : real) : (term631 c x0) = (term598 c x0).
Proof. exact (MK_COMB (@lem5318393 c x0) (@lem5318394)). Qed.
Lemma lem5318396 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term598 c x0.
Proof. exact (EQ_MP (@lem5318395 c x0) (@lem5318390 s c l x0 h1)). Qed.
Lemma lem5318398 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5318399 : term468 = term469.
Proof. exact (@lem5318398 term360 term370). Qed.
Lemma lem5318400 : term370 = term370.
Proof. exact (eq_refl term370). Qed.
Lemma lem5318402 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318403 : term360 = term452.
Proof. exact (@lem5318402 (NUMERAL 0)). Qed.
Lemma lem5318404 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318405 : term453 = term454.
Proof. exact (MK_COMB (@lem5318404) (@lem5318403)). Qed.
Lemma lem5318406 : term469 = term470.
Proof. exact (MK_COMB (@lem5318405) (@lem5318400)). Qed.
Lemma lem5318407 : term471.
Proof. exact (@lem1980255 term360 term366 term394 term394). Qed.
Lemma lem5318409 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318410 : term401 = term402.
Proof. exact (@lem5318409 (NUMERAL 0) term389). Qed.
Lemma lem5318411 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318412 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318413 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318412 h1) (fun h1 : term402 = True => @lem5318411)). Qed.
Lemma lem5318414 : term402 = True.
Proof. exact (EQ_MP (@lem5318413) (@lem5318411)). Qed.
Lemma lem5318415 : term401 = True.
Proof. exact (TRANS (@lem5318410) (@lem5318414)). Qed.
Lemma lem5318416 : True = term401.
Proof. exact (SYM (@lem5318415)). Qed.
Lemma lem5318417 : term401.
Proof. exact (EQ_MP (@lem5318416) (@lem0)). Qed.
Lemma lem5318418 : term472.
Proof. exact (@lem5318407 (@lem5318417)). Qed.
Lemma lem5318420 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318421 : term396 = term397.
Proof. exact (@lem5318420 (NUMERAL 0) term371). Qed.
Lemma lem5318422 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5318423 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5318424 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5318423 h1) (fun h1 : term397 = True => @lem5318422)). Qed.
Lemma lem5318425 : term397 = True.
Proof. exact (EQ_MP (@lem5318424) (@lem5318422)). Qed.
Lemma lem5318426 : term396 = True.
Proof. exact (TRANS (@lem5318421) (@lem5318425)). Qed.
Lemma lem5318427 : True = term396.
Proof. exact (SYM (@lem5318426)). Qed.
Lemma lem5318428 : term396.
Proof. exact (EQ_MP (@lem5318427) (@lem0)). Qed.
Lemma lem5318429 : term470 = term473.
Proof. exact (@lem5318418 (@lem5318428)). Qed.
Lemma lem5318431 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318432 : term416 = term417.
Proof. exact (@lem5318431 term389 term389). Qed.
Lemma lem5318433 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318434 : term419 = term389.
Proof. exact (EQ_MP (@lem5318433) (@lem940073)). Qed.
Lemma lem5318435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318436 : term417 = term394.
Proof. exact (MK_COMB (@lem5318435) (@lem5318434)). Qed.
Lemma lem5318437 : term416 = term394.
Proof. exact (TRANS (@lem5318432) (@lem5318436)). Qed.
Lemma lem5318439 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5318440 : term474 = term360.
Proof. exact (@lem5318439 term371). Qed.
Lemma lem5318441 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318442 : term475 = term453.
Proof. exact (MK_COMB (@lem5318441) (@lem5318440)). Qed.
Lemma lem5318443 : term473 = term401.
Proof. exact (MK_COMB (@lem5318442) (@lem5318437)). Qed.
Lemma lem5318445 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318446 : term401 = term402.
Proof. exact (@lem5318445 (NUMERAL 0) term389). Qed.
Lemma lem5318447 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318448 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318449 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318448 h1) (fun h1 : term402 = True => @lem5318447)). Qed.
Lemma lem5318450 : term402 = True.
Proof. exact (EQ_MP (@lem5318449) (@lem5318447)). Qed.
Lemma lem5318451 : term401 = True.
Proof. exact (TRANS (@lem5318446) (@lem5318450)). Qed.
Lemma lem5318452 : term473 = True.
Proof. exact (TRANS (@lem5318443) (@lem5318451)). Qed.
Lemma lem5318453 : term470 = True.
Proof. exact (TRANS (@lem5318429) (@lem5318452)). Qed.
Lemma lem5318454 : term469 = True.
Proof. exact (TRANS (@lem5318406) (@lem5318453)). Qed.
Lemma lem5318455 : term468 = True.
Proof. exact (TRANS (@lem5318399) (@lem5318454)). Qed.
Lemma lem5318456 : True = term468.
Proof. exact (SYM (@lem5318455)). Qed.
Lemma lem5318457 : term468.
Proof. exact (EQ_MP (@lem5318456) (@lem0)). Qed.
Lemma lem5318458 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term476 c l.
Proof. exact (conj (@lem5318457) (@lem5318318 s c l x0 h1)). Qed.
Lemma lem5318460 (x : real) (y : real) : term477 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5318461 (c : real) (l : real) : term478 c l.
Proof. exact (@lem5318460 term370 (term356 c l)). Qed.
Lemma lem5318462 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term479 c l.
Proof. exact (@lem5318461 c l (@lem5318458 s c l x0 h1)). Qed.
Lemma lem5318463 (c : real) (l : real) : (term480 c l) = (term481 c l).
Proof. exact (@lem1982781 (term357 c) term370 l). Qed.
Lemma lem5318464 (l : real) : (term382 l) = (term382 l).
Proof. exact (eq_refl (term382 l)). Qed.
Lemma lem5318465 (c : real) : (term482 c) = (term483 c).
Proof. exact (@lem1982749 term370 term385 c). Qed.
Lemma lem5318467 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5318468 : term385 = term388.
Proof. exact (@lem5318467 term389). Qed.
Lemma lem5318471 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem5318472 : term485 = term486.
Proof. exact (MK_COMB (@lem5318471) (@lem5318468)). Qed.
Lemma lem5318473 : term486 = term487.
Proof. exact (@lem1981613 term394 term385 term366 term394). Qed.
Lemma lem5318475 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318476 : term432 = term433.
Proof. exact (@lem5318475 term371 term389). Qed.
Lemma lem5318477 : term434 = term399.
Proof. exact (@lem996237 term399). Qed.
Lemma lem5318478 : (term434 = term399) = (term435 = term371).
Proof. exact (@lem1007663 term399 (BIT1 0) term399). Qed.
Lemma lem5318479 : term435 = term371.
Proof. exact (EQ_MP (@lem5318478) (@lem5318477)). Qed.
Lemma lem5318480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318481 : term433 = term366.
Proof. exact (MK_COMB (@lem5318480) (@lem5318479)). Qed.
Lemma lem5318482 : term432 = term366.
Proof. exact (TRANS (@lem5318476) (@lem5318481)). Qed.
Lemma lem5318484 (m : nat) (n : nat) : (term488 m n) = (term407 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5318485 : term489 = term490.
Proof. exact (@lem5318484 term389 term389). Qed.
Lemma lem5318486 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318487 : term419 = term389.
Proof. exact (EQ_MP (@lem5318486) (@lem940073)). Qed.
Lemma lem5318488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318489 : term417 = term394.
Proof. exact (MK_COMB (@lem5318488) (@lem5318487)). Qed.
Lemma lem5318490 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318491 : term490 = term385.
Proof. exact (MK_COMB (@lem5318490) (@lem5318489)). Qed.
Lemma lem5318492 : term489 = term385.
Proof. exact (TRANS (@lem5318485) (@lem5318491)). Qed.
Lemma lem5318493 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5318494 : term491 = term492.
Proof. exact (MK_COMB (@lem5318493) (@lem5318492)). Qed.
Lemma lem5318495 : term487 = term437.
Proof. exact (MK_COMB (@lem5318494) (@lem5318482)). Qed.
Lemma lem5318496 : term486 = term437.
Proof. exact (TRANS (@lem5318473) (@lem5318495)). Qed.
Lemma lem5318499 : term485 = term437.
Proof. exact (TRANS (@lem5318472) (@lem5318496)). Qed.
Lemma lem5318500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318501 : term493 = term439.
Proof. exact (MK_COMB (@lem5318500) (@lem5318499)). Qed.
Lemma lem5318502 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5318503 (c : real) : (term483 c) = (term440 c).
Proof. exact (MK_COMB (@lem5318501) (@lem5318502 c)). Qed.
Lemma lem5318504 (c : real) : (term482 c) = (term440 c).
Proof. exact (TRANS (@lem5318465 c) (@lem5318503 c)). Qed.
Lemma lem5318505 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318506 (c : real) : (term494 c) = (term495 c).
Proof. exact (MK_COMB (@lem5318505) (@lem5318504 c)). Qed.
Lemma lem5318507 (c : real) (l : real) : (term481 c l) = (term496 c l).
Proof. exact (MK_COMB (@lem5318506 c) (@lem5318464 l)). Qed.
Lemma lem5318508 (c : real) (l : real) : (term480 c l) = (term496 c l).
Proof. exact (TRANS (@lem5318463 c l) (@lem5318507 c l)). Qed.
Lemma lem5318509 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5318510 (c : real) (l : real) : (term497 c l) = (term498 c l).
Proof. exact (MK_COMB (@lem5318509) (@lem5318508 c l)). Qed.
Lemma lem5318511 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318512 (c : real) (l : real) : (term479 c l) = (term499 c l).
Proof. exact (MK_COMB (@lem5318510 c l) (@lem5318511)). Qed.
Lemma lem5318513 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term499 c l.
Proof. exact (EQ_MP (@lem5318512 c l) (@lem5318462 s c l x0 h1)). Qed.
Lemma lem5318515 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5318516 : term449 = term401.
Proof. exact (@lem5318515 term360 term394). Qed.
Lemma lem5318518 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318519 : term394 = term451.
Proof. exact (@lem5318518 term389). Qed.
Lemma lem5318521 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318522 : term360 = term452.
Proof. exact (@lem5318521 (NUMERAL 0)). Qed.
Lemma lem5318523 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318524 : term453 = term454.
Proof. exact (MK_COMB (@lem5318523) (@lem5318522)). Qed.
Lemma lem5318525 : term401 = term455.
Proof. exact (MK_COMB (@lem5318524) (@lem5318519)). Qed.
Lemma lem5318526 : term456.
Proof. exact (@lem1980255 term360 term394 term394 term394). Qed.
Lemma lem5318528 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318529 : term401 = term402.
Proof. exact (@lem5318528 (NUMERAL 0) term389). Qed.
Lemma lem5318530 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318531 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318532 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318531 h1) (fun h1 : term402 = True => @lem5318530)). Qed.
Lemma lem5318533 : term402 = True.
Proof. exact (EQ_MP (@lem5318532) (@lem5318530)). Qed.
Lemma lem5318534 : term401 = True.
Proof. exact (TRANS (@lem5318529) (@lem5318533)). Qed.
Lemma lem5318535 : True = term401.
Proof. exact (SYM (@lem5318534)). Qed.
Lemma lem5318536 : term401.
Proof. exact (EQ_MP (@lem5318535) (@lem0)). Qed.
Lemma lem5318537 : term457.
Proof. exact (@lem5318526 (@lem5318536)). Qed.
Lemma lem5318539 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318540 : term401 = term402.
Proof. exact (@lem5318539 (NUMERAL 0) term389). Qed.
Lemma lem5318541 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318542 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318543 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318542 h1) (fun h1 : term402 = True => @lem5318541)). Qed.
Lemma lem5318544 : term402 = True.
Proof. exact (EQ_MP (@lem5318543) (@lem5318541)). Qed.
Lemma lem5318545 : term401 = True.
Proof. exact (TRANS (@lem5318540) (@lem5318544)). Qed.
Lemma lem5318546 : True = term401.
Proof. exact (SYM (@lem5318545)). Qed.
Lemma lem5318547 : term401.
Proof. exact (EQ_MP (@lem5318546) (@lem0)). Qed.
Lemma lem5318548 : term455 = term458.
Proof. exact (@lem5318537 (@lem5318547)). Qed.
Lemma lem5318550 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318551 : term416 = term417.
Proof. exact (@lem5318550 term389 term389). Qed.
Lemma lem5318552 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318553 : term419 = term389.
Proof. exact (EQ_MP (@lem5318552) (@lem940073)). Qed.
Lemma lem5318554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318555 : term417 = term394.
Proof. exact (MK_COMB (@lem5318554) (@lem5318553)). Qed.
Lemma lem5318556 : term416 = term394.
Proof. exact (TRANS (@lem5318551) (@lem5318555)). Qed.
Lemma lem5318558 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5318559 : term460 = term360.
Proof. exact (@lem5318558 term389). Qed.
Lemma lem5318560 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318561 : term461 = term453.
Proof. exact (MK_COMB (@lem5318560) (@lem5318559)). Qed.
Lemma lem5318562 : term458 = term401.
Proof. exact (MK_COMB (@lem5318561) (@lem5318556)). Qed.
Lemma lem5318564 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318565 : term401 = term402.
Proof. exact (@lem5318564 (NUMERAL 0) term389). Qed.
Lemma lem5318566 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318567 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318568 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318567 h1) (fun h1 : term402 = True => @lem5318566)). Qed.
Lemma lem5318569 : term402 = True.
Proof. exact (EQ_MP (@lem5318568) (@lem5318566)). Qed.
Lemma lem5318570 : term401 = True.
Proof. exact (TRANS (@lem5318565) (@lem5318569)). Qed.
Lemma lem5318571 : term458 = True.
Proof. exact (TRANS (@lem5318562) (@lem5318570)). Qed.
Lemma lem5318572 : term455 = True.
Proof. exact (TRANS (@lem5318548) (@lem5318571)). Qed.
Lemma lem5318573 : term401 = True.
Proof. exact (TRANS (@lem5318525) (@lem5318572)). Qed.
Lemma lem5318574 : term449 = True.
Proof. exact (TRANS (@lem5318516) (@lem5318573)). Qed.
Lemma lem5318575 : True = term449.
Proof. exact (SYM (@lem5318574)). Qed.
Lemma lem5318576 : term449.
Proof. exact (EQ_MP (@lem5318575) (@lem0)). Qed.
Lemma lem5318577 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term634 c l x0.
Proof. exact (conj (@lem5318576) (@lem5318321 s c l x0 h1)). Qed.
Lemma lem5318579 (x : real) (y : real) : term477 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5318580 (c : real) (l : real) (x0 : real) : term635 c l x0.
Proof. exact (@lem5318579 term394 (term620 c l x0)). Qed.
Lemma lem5318581 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term636 c l x0.
Proof. exact (@lem5318580 c l x0 (@lem5318577 s c l x0 h1)). Qed.
Lemma lem5318582 (c : real) (l : real) (x0 : real) : (term637 c l x0) = (term620 c l x0).
Proof. exact (@lem1982733 (term620 c l x0)). Qed.
Lemma lem5318583 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5318584 (c : real) (l : real) (x0 : real) : (term638 c l x0) = (term622 c l x0).
Proof. exact (MK_COMB (@lem5318583) (@lem5318582 c l x0)). Qed.
Lemma lem5318585 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318586 (c : real) (l : real) (x0 : real) : (term636 c l x0) = (term623 c l x0).
Proof. exact (MK_COMB (@lem5318584 c l x0) (@lem5318585)). Qed.
Lemma lem5318587 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term623 c l x0.
Proof. exact (EQ_MP (@lem5318586 c l x0) (@lem5318581 s c l x0 h1)). Qed.
Lemma lem5318588 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term639 x0 c l.
Proof. exact (conj (@lem5318587 s c l x0 h1) (@lem5318513 s c l x0 h1)). Qed.
Lemma lem5318590 (x : real) (y : real) : term640 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem5318591 (x0 : real) (c : real) (l : real) : term641 x0 c l.
Proof. exact (@lem5318590 (term620 c l x0) (term496 c l)). Qed.
Lemma lem5318592 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term642 x0 c l.
Proof. exact (@lem5318591 x0 c l (@lem5318588 s c l x0 h1)). Qed.
Lemma lem5318593 (c : real) (x0 : real) (l : real) : (term643 x0 c l) = (term644 c x0 l).
Proof. exact (@lem1982753 (term440 c) (term440 c) (term619 l x0) (term382 l)). Qed.
Lemma lem5318594 (c : real) : (term645 c) = (term646 c).
Proof. exact (@lem1982711 term437 term437 c). Qed.
Lemma lem5318600 : term647.
Proof. exact (@lem1981473 term385 term366 term385 term366 term385 term394). Qed.
Lemma lem5318602 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318603 : term396 = term397.
Proof. exact (@lem5318602 (NUMERAL 0) term371). Qed.
Lemma lem5318604 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5318605 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5318606 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5318605 h1) (fun h1 : term397 = True => @lem5318604)). Qed.
Lemma lem5318607 : term397 = True.
Proof. exact (EQ_MP (@lem5318606) (@lem5318604)). Qed.
Lemma lem5318608 : term396 = True.
Proof. exact (TRANS (@lem5318603) (@lem5318607)). Qed.
Lemma lem5318609 : True = term396.
Proof. exact (SYM (@lem5318608)). Qed.
Lemma lem5318610 : term396.
Proof. exact (EQ_MP (@lem5318609) (@lem0)). Qed.
Lemma lem5318611 : term648.
Proof. exact (@lem5318600 (@lem5318610)). Qed.
Lemma lem5318613 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318614 : term396 = term397.
Proof. exact (@lem5318613 (NUMERAL 0) term371). Qed.
Lemma lem5318615 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5318616 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5318617 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5318616 h1) (fun h1 : term397 = True => @lem5318615)). Qed.
Lemma lem5318618 : term397 = True.
Proof. exact (EQ_MP (@lem5318617) (@lem5318615)). Qed.
Lemma lem5318619 : term396 = True.
Proof. exact (TRANS (@lem5318614) (@lem5318618)). Qed.
Lemma lem5318620 : True = term396.
Proof. exact (SYM (@lem5318619)). Qed.
Lemma lem5318621 : term396.
Proof. exact (EQ_MP (@lem5318620) (@lem0)). Qed.
Lemma lem5318622 : term649.
Proof. exact (@lem5318611 (@lem5318621)). Qed.
Lemma lem5318624 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318625 : term401 = term402.
Proof. exact (@lem5318624 (NUMERAL 0) term389). Qed.
Lemma lem5318626 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318627 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318628 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318627 h1) (fun h1 : term402 = True => @lem5318626)). Qed.
Lemma lem5318629 : term402 = True.
Proof. exact (EQ_MP (@lem5318628) (@lem5318626)). Qed.
Lemma lem5318630 : term401 = True.
Proof. exact (TRANS (@lem5318625) (@lem5318629)). Qed.
Lemma lem5318631 : True = term401.
Proof. exact (SYM (@lem5318630)). Qed.
Lemma lem5318632 : term401.
Proof. exact (EQ_MP (@lem5318631) (@lem0)). Qed.
Lemma lem5318633 : term650.
Proof. exact (@lem5318622 (@lem5318632)). Qed.
Lemma lem5318635 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318636 : term408 = term409.
Proof. exact (@lem5318635 term389 term371). Qed.
Lemma lem5318637 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5318638 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5318639 : term411 = term371.
Proof. exact (EQ_MP (@lem5318638) (@lem5318637)). Qed.
Lemma lem5318640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318641 : term412 = term366.
Proof. exact (MK_COMB (@lem5318640) (@lem5318639)). Qed.
Lemma lem5318642 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318643 : term409 = term413.
Proof. exact (MK_COMB (@lem5318642) (@lem5318641)). Qed.
Lemma lem5318644 : term408 = term413.
Proof. exact (TRANS (@lem5318636) (@lem5318643)). Qed.
Lemma lem5318646 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318647 : term408 = term409.
Proof. exact (@lem5318646 term389 term371). Qed.
Lemma lem5318648 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5318649 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5318650 : term411 = term371.
Proof. exact (EQ_MP (@lem5318649) (@lem5318648)). Qed.
Lemma lem5318651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318652 : term412 = term366.
Proof. exact (MK_COMB (@lem5318651) (@lem5318650)). Qed.
Lemma lem5318653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318654 : term409 = term413.
Proof. exact (MK_COMB (@lem5318653) (@lem5318652)). Qed.
Lemma lem5318655 : term408 = term413.
Proof. exact (TRANS (@lem5318647) (@lem5318654)). Qed.
Lemma lem5318656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318657 : term513 = term514.
Proof. exact (MK_COMB (@lem5318656) (@lem5318655)). Qed.
Lemma lem5318658 : term651 = term652.
Proof. exact (MK_COMB (@lem5318657) (@lem5318644)). Qed.
Lemma lem5318659 : term652 = term653.
Proof. exact (@lem1367763 term371 term371). Qed.
Lemma lem5318660 : term654 = term524.
Proof. exact (@lem706951). Qed.
Lemma lem5318661 : (term654 = term524) = (term655 = term526).
Proof. exact (@lem1006570 term399 term399 term524). Qed.
Lemma lem5318662 : term655 = term526.
Proof. exact (EQ_MP (@lem5318661) (@lem5318660)). Qed.
Lemma lem5318663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318664 : term656 = term527.
Proof. exact (MK_COMB (@lem5318663) (@lem5318662)). Qed.
Lemma lem5318665 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318666 : term653 = term657.
Proof. exact (MK_COMB (@lem5318665) (@lem5318664)). Qed.
Lemma lem5318667 : term652 = term657.
Proof. exact (TRANS (@lem5318659) (@lem5318666)). Qed.
Lemma lem5318668 : term651 = term657.
Proof. exact (TRANS (@lem5318658) (@lem5318667)). Qed.
Lemma lem5318669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318670 : term658 = term659.
Proof. exact (MK_COMB (@lem5318669) (@lem5318668)). Qed.
Lemma lem5318671 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem5318672 : term660 = term661.
Proof. exact (MK_COMB (@lem5318670) (@lem5318671)). Qed.
Lemma lem5318674 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318675 : term661 = term662.
Proof. exact (@lem5318674 term526 term389). Qed.
Lemma lem5318676 : term663 = term524.
Proof. exact (@lem996237 term524). Qed.
Lemma lem5318677 : (term663 = term524) = (term664 = term526).
Proof. exact (@lem1007663 term524 (BIT1 0) term524). Qed.
Lemma lem5318678 : term664 = term526.
Proof. exact (EQ_MP (@lem5318677) (@lem5318676)). Qed.
Lemma lem5318679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318680 : term665 = term527.
Proof. exact (MK_COMB (@lem5318679) (@lem5318678)). Qed.
Lemma lem5318681 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318682 : term662 = term657.
Proof. exact (MK_COMB (@lem5318681) (@lem5318680)). Qed.
Lemma lem5318683 : term661 = term657.
Proof. exact (TRANS (@lem5318675) (@lem5318682)). Qed.
Lemma lem5318684 : term660 = term657.
Proof. exact (TRANS (@lem5318672) (@lem5318683)). Qed.
Lemma lem5318686 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318687 : term521 = term522.
Proof. exact (@lem5318686 term371 term371). Qed.
Lemma lem5318688 : (term418 = (BIT1 0)) = (term523 = term524).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318689 : term523 = term524.
Proof. exact (EQ_MP (@lem5318688) (@lem940073)). Qed.
Lemma lem5318690 : (term523 = term524) = (term525 = term526).
Proof. exact (@lem1008952 term399 term524). Qed.
Lemma lem5318691 : term525 = term526.
Proof. exact (EQ_MP (@lem5318690) (@lem5318689)). Qed.
Lemma lem5318692 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318693 : term522 = term527.
Proof. exact (MK_COMB (@lem5318692) (@lem5318691)). Qed.
Lemma lem5318694 : term521 = term527.
Proof. exact (TRANS (@lem5318687) (@lem5318693)). Qed.
Lemma lem5318695 : term430 = term430.
Proof. exact (eq_refl term430). Qed.
Lemma lem5318696 : term666 = term667.
Proof. exact (MK_COMB (@lem5318695) (@lem5318694)). Qed.
Lemma lem5318698 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318699 : term667 = term668.
Proof. exact (@lem5318698 term389 term526). Qed.
Lemma lem5318700 : term669 = term524.
Proof. exact (@lem996238 term524). Qed.
Lemma lem5318701 : (term669 = term524) = (term670 = term526).
Proof. exact (@lem1007663 (BIT1 0) term524 term524). Qed.
Lemma lem5318702 : term670 = term526.
Proof. exact (EQ_MP (@lem5318701) (@lem5318700)). Qed.
Lemma lem5318703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318704 : term671 = term527.
Proof. exact (MK_COMB (@lem5318703) (@lem5318702)). Qed.
Lemma lem5318705 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318706 : term668 = term657.
Proof. exact (MK_COMB (@lem5318705) (@lem5318704)). Qed.
Lemma lem5318707 : term667 = term657.
Proof. exact (TRANS (@lem5318699) (@lem5318706)). Qed.
Lemma lem5318708 : term666 = term657.
Proof. exact (TRANS (@lem5318696) (@lem5318707)). Qed.
Lemma lem5318709 : term657 = term666.
Proof. exact (SYM (@lem5318708)). Qed.
Lemma lem5318710 : term660 = term666.
Proof. exact (TRANS (@lem5318684) (@lem5318709)). Qed.
Lemma lem5318712 : term672 = term388.
Proof. exact (@lem5318633 (@lem5318710)). Qed.
Lemma lem5318714 (x : real) : (term531 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5318715 : term388 = term385.
Proof. exact (@lem5318714 term385). Qed.
Lemma lem5318716 : term672 = term385.
Proof. exact (TRANS (@lem5318712) (@lem5318715)). Qed.
Lemma lem5318717 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318718 : term673 = term430.
Proof. exact (MK_COMB (@lem5318717) (@lem5318716)). Qed.
Lemma lem5318719 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5318720 (c : real) : (term646 c) = (term357 c).
Proof. exact (MK_COMB (@lem5318718) (@lem5318719 c)). Qed.
Lemma lem5318721 (c : real) : (term645 c) = (term357 c).
Proof. exact (TRANS (@lem5318594 c) (@lem5318720 c)). Qed.
Lemma lem5318722 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318723 (c : real) : (term674 c) = (term675 c).
Proof. exact (MK_COMB (@lem5318722) (@lem5318721 c)). Qed.
Lemma lem5318724 (l : real) (x0 : real) : (term676 x0 l) = (term677 l x0).
Proof. exact (@lem1982759 (term440 l) (term382 l) x0). Qed.
Lemma lem5318725 (l : real) : (term506 l) = (term507 l).
Proof. exact (@lem1982711 term437 term370 l). Qed.
Lemma lem5318731 : term508.
Proof. exact (@lem1981473 term385 term366 term394 term366 term360 term394). Qed.
Lemma lem5318733 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318734 : term396 = term397.
Proof. exact (@lem5318733 (NUMERAL 0) term371). Qed.
Lemma lem5318735 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5318736 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5318737 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5318736 h1) (fun h1 : term397 = True => @lem5318735)). Qed.
Lemma lem5318738 : term397 = True.
Proof. exact (EQ_MP (@lem5318737) (@lem5318735)). Qed.
Lemma lem5318739 : term396 = True.
Proof. exact (TRANS (@lem5318734) (@lem5318738)). Qed.
Lemma lem5318740 : True = term396.
Proof. exact (SYM (@lem5318739)). Qed.
Lemma lem5318741 : term396.
Proof. exact (EQ_MP (@lem5318740) (@lem0)). Qed.
Lemma lem5318742 : term509.
Proof. exact (@lem5318731 (@lem5318741)). Qed.
Lemma lem5318744 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318745 : term396 = term397.
Proof. exact (@lem5318744 (NUMERAL 0) term371). Qed.
Lemma lem5318746 : term398 = term399.
Proof. exact (@lem912803). Qed.
Lemma lem5318747 (h1 : term398 = term399) : term397 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term399 h1). Qed.
Lemma lem5318748 : (term398 = term399) = (term397 = True).
Proof. exact (prop_ext (fun h1 : term398 = term399 => @lem5318747 h1) (fun h1 : term397 = True => @lem5318746)). Qed.
Lemma lem5318749 : term397 = True.
Proof. exact (EQ_MP (@lem5318748) (@lem5318746)). Qed.
Lemma lem5318750 : term396 = True.
Proof. exact (TRANS (@lem5318745) (@lem5318749)). Qed.
Lemma lem5318751 : True = term396.
Proof. exact (SYM (@lem5318750)). Qed.
Lemma lem5318752 : term396.
Proof. exact (EQ_MP (@lem5318751) (@lem0)). Qed.
Lemma lem5318753 : term510.
Proof. exact (@lem5318742 (@lem5318752)). Qed.
Lemma lem5318755 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318756 : term401 = term402.
Proof. exact (@lem5318755 (NUMERAL 0) term389). Qed.
Lemma lem5318757 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318758 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318759 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318758 h1) (fun h1 : term402 = True => @lem5318757)). Qed.
Lemma lem5318760 : term402 = True.
Proof. exact (EQ_MP (@lem5318759) (@lem5318757)). Qed.
Lemma lem5318761 : term401 = True.
Proof. exact (TRANS (@lem5318756) (@lem5318760)). Qed.
Lemma lem5318762 : True = term401.
Proof. exact (SYM (@lem5318761)). Qed.
Lemma lem5318763 : term401.
Proof. exact (EQ_MP (@lem5318762) (@lem0)). Qed.
Lemma lem5318764 : term511.
Proof. exact (@lem5318753 (@lem5318763)). Qed.
Lemma lem5318766 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318767 : term512 = term412.
Proof. exact (@lem5318766 term389 term371). Qed.
Lemma lem5318768 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5318769 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5318770 : term411 = term371.
Proof. exact (EQ_MP (@lem5318769) (@lem5318768)). Qed.
Lemma lem5318771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318772 : term412 = term366.
Proof. exact (MK_COMB (@lem5318771) (@lem5318770)). Qed.
Lemma lem5318773 : term512 = term366.
Proof. exact (TRANS (@lem5318767) (@lem5318772)). Qed.
Lemma lem5318775 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318776 : term408 = term409.
Proof. exact (@lem5318775 term389 term371). Qed.
Lemma lem5318777 : term410 = term399.
Proof. exact (@lem996238 term399). Qed.
Lemma lem5318778 : (term410 = term399) = (term411 = term371).
Proof. exact (@lem1007663 (BIT1 0) term399 term399). Qed.
Lemma lem5318779 : term411 = term371.
Proof. exact (EQ_MP (@lem5318778) (@lem5318777)). Qed.
Lemma lem5318780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318781 : term412 = term366.
Proof. exact (MK_COMB (@lem5318780) (@lem5318779)). Qed.
Lemma lem5318782 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318783 : term409 = term413.
Proof. exact (MK_COMB (@lem5318782) (@lem5318781)). Qed.
Lemma lem5318784 : term408 = term413.
Proof. exact (TRANS (@lem5318776) (@lem5318783)). Qed.
Lemma lem5318785 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318786 : term513 = term514.
Proof. exact (MK_COMB (@lem5318785) (@lem5318784)). Qed.
Lemma lem5318787 : term515 = term516.
Proof. exact (MK_COMB (@lem5318786) (@lem5318773)). Qed.
Lemma lem5318789 (m : nat) : (term517 m) = term360.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5318790 : term516 = term360.
Proof. exact (@lem5318789 term371). Qed.
Lemma lem5318791 : term515 = term360.
Proof. exact (TRANS (@lem5318787) (@lem5318790)). Qed.
Lemma lem5318792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318793 : term518 = term519.
Proof. exact (MK_COMB (@lem5318792) (@lem5318791)). Qed.
Lemma lem5318794 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem5318795 : term520 = term460.
Proof. exact (MK_COMB (@lem5318793) (@lem5318794)). Qed.
Lemma lem5318797 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5318798 : term460 = term360.
Proof. exact (@lem5318797 term389). Qed.
Lemma lem5318799 : term520 = term360.
Proof. exact (TRANS (@lem5318795) (@lem5318798)). Qed.
Lemma lem5318801 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318802 : term521 = term522.
Proof. exact (@lem5318801 term371 term371). Qed.
Lemma lem5318803 : (term418 = (BIT1 0)) = (term523 = term524).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318804 : term523 = term524.
Proof. exact (EQ_MP (@lem5318803) (@lem940073)). Qed.
Lemma lem5318805 : (term523 = term524) = (term525 = term526).
Proof. exact (@lem1008952 term399 term524). Qed.
Lemma lem5318806 : term525 = term526.
Proof. exact (EQ_MP (@lem5318805) (@lem5318804)). Qed.
Lemma lem5318807 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318808 : term522 = term527.
Proof. exact (MK_COMB (@lem5318807) (@lem5318806)). Qed.
Lemma lem5318809 : term521 = term527.
Proof. exact (TRANS (@lem5318802) (@lem5318808)). Qed.
Lemma lem5318810 : term519 = term519.
Proof. exact (eq_refl term519). Qed.
Lemma lem5318811 : term528 = term529.
Proof. exact (MK_COMB (@lem5318810) (@lem5318809)). Qed.
Lemma lem5318813 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5318814 : term529 = term360.
Proof. exact (@lem5318813 term526). Qed.
Lemma lem5318815 : term528 = term360.
Proof. exact (TRANS (@lem5318811) (@lem5318814)). Qed.
Lemma lem5318816 : term360 = term528.
Proof. exact (SYM (@lem5318815)). Qed.
Lemma lem5318817 : term520 = term528.
Proof. exact (TRANS (@lem5318799) (@lem5318816)). Qed.
Lemma lem5318819 : term530 = term452.
Proof. exact (@lem5318764 (@lem5318817)). Qed.
Lemma lem5318821 (x : real) : (term531 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5318822 : term452 = term360.
Proof. exact (@lem5318821 term360). Qed.
Lemma lem5318823 : term530 = term360.
Proof. exact (TRANS (@lem5318819) (@lem5318822)). Qed.
Lemma lem5318824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318825 : term532 = term519.
Proof. exact (MK_COMB (@lem5318824) (@lem5318823)). Qed.
Lemma lem5318826 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5318827 (l : real) : (term507 l) = (term533 l).
Proof. exact (MK_COMB (@lem5318825) (@lem5318826 l)). Qed.
Lemma lem5318828 (l : real) : (term506 l) = (term533 l).
Proof. exact (TRANS (@lem5318725 l) (@lem5318827 l)). Qed.
Lemma lem5318829 (l : real) : (term533 l) = term360.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5318830 (l : real) : (term506 l) = term360.
Proof. exact (TRANS (@lem5318828 l) (@lem5318829 l)). Qed.
Lemma lem5318831 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318832 (l : real) : (term534 l) = term535.
Proof. exact (MK_COMB (@lem5318831) (@lem5318830 l)). Qed.
Lemma lem5318833 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem5318834 (l : real) (x0 : real) : (term677 l x0) = (term678 x0).
Proof. exact (MK_COMB (@lem5318832 l) (@lem5318833 x0)). Qed.
Lemma lem5318835 (l : real) (x0 : real) : (term676 x0 l) = (term678 x0).
Proof. exact (TRANS (@lem5318724 l x0) (@lem5318834 l x0)). Qed.
Lemma lem5318836 (x0 : real) : (term678 x0) = x0.
Proof. exact (@lem1982721 x0). Qed.
Lemma lem5318837 (l : real) (x0 : real) : (term676 x0 l) = x0.
Proof. exact (TRANS (@lem5318835 l x0) (@lem5318836 x0)). Qed.
Lemma lem5318838 (l : real) (c : real) (x0 : real) : (term644 c x0 l) = (term356 c x0).
Proof. exact (MK_COMB (@lem5318723 c) (@lem5318837 l x0)). Qed.
Lemma lem5318839 (l : real) (c : real) (x0 : real) : (term643 x0 c l) = (term356 c x0).
Proof. exact (TRANS (@lem5318593 c x0 l) (@lem5318838 l c x0)). Qed.
Lemma lem5318840 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5318841 (l : real) (c : real) (x0 : real) : (term679 x0 c l) = (term359 c x0).
Proof. exact (MK_COMB (@lem5318840) (@lem5318839 l c x0)). Qed.
Lemma lem5318842 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318843 (l : real) (c : real) (x0 : real) : (term642 x0 c l) = (term361 c x0).
Proof. exact (MK_COMB (@lem5318841 l c x0) (@lem5318842)). Qed.
Lemma lem5318844 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term361 c x0.
Proof. exact (EQ_MP (@lem5318843 l c x0) (@lem5318592 s c l x0 h1)). Qed.
Lemma lem5318846 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5318847 : term449 = term401.
Proof. exact (@lem5318846 term360 term394). Qed.
Lemma lem5318849 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318850 : term394 = term451.
Proof. exact (@lem5318849 term389). Qed.
Lemma lem5318852 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318853 : term360 = term452.
Proof. exact (@lem5318852 (NUMERAL 0)). Qed.
Lemma lem5318854 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318855 : term453 = term454.
Proof. exact (MK_COMB (@lem5318854) (@lem5318853)). Qed.
Lemma lem5318856 : term401 = term455.
Proof. exact (MK_COMB (@lem5318855) (@lem5318850)). Qed.
Lemma lem5318857 : term456.
Proof. exact (@lem1980255 term360 term394 term394 term394). Qed.
Lemma lem5318859 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318860 : term401 = term402.
Proof. exact (@lem5318859 (NUMERAL 0) term389). Qed.
Lemma lem5318861 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318862 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318863 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318862 h1) (fun h1 : term402 = True => @lem5318861)). Qed.
Lemma lem5318864 : term402 = True.
Proof. exact (EQ_MP (@lem5318863) (@lem5318861)). Qed.
Lemma lem5318865 : term401 = True.
Proof. exact (TRANS (@lem5318860) (@lem5318864)). Qed.
Lemma lem5318866 : True = term401.
Proof. exact (SYM (@lem5318865)). Qed.
Lemma lem5318867 : term401.
Proof. exact (EQ_MP (@lem5318866) (@lem0)). Qed.
Lemma lem5318868 : term457.
Proof. exact (@lem5318857 (@lem5318867)). Qed.
Lemma lem5318870 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318871 : term401 = term402.
Proof. exact (@lem5318870 (NUMERAL 0) term389). Qed.
Lemma lem5318872 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318873 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318874 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318873 h1) (fun h1 : term402 = True => @lem5318872)). Qed.
Lemma lem5318875 : term402 = True.
Proof. exact (EQ_MP (@lem5318874) (@lem5318872)). Qed.
Lemma lem5318876 : term401 = True.
Proof. exact (TRANS (@lem5318871) (@lem5318875)). Qed.
Lemma lem5318877 : True = term401.
Proof. exact (SYM (@lem5318876)). Qed.
Lemma lem5318878 : term401.
Proof. exact (EQ_MP (@lem5318877) (@lem0)). Qed.
Lemma lem5318879 : term455 = term458.
Proof. exact (@lem5318868 (@lem5318878)). Qed.
Lemma lem5318881 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318882 : term416 = term417.
Proof. exact (@lem5318881 term389 term389). Qed.
Lemma lem5318883 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318884 : term419 = term389.
Proof. exact (EQ_MP (@lem5318883) (@lem940073)). Qed.
Lemma lem5318885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318886 : term417 = term394.
Proof. exact (MK_COMB (@lem5318885) (@lem5318884)). Qed.
Lemma lem5318887 : term416 = term394.
Proof. exact (TRANS (@lem5318882) (@lem5318886)). Qed.
Lemma lem5318889 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5318890 : term460 = term360.
Proof. exact (@lem5318889 term389). Qed.
Lemma lem5318891 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5318892 : term461 = term453.
Proof. exact (MK_COMB (@lem5318891) (@lem5318890)). Qed.
Lemma lem5318893 : term458 = term401.
Proof. exact (MK_COMB (@lem5318892) (@lem5318887)). Qed.
Lemma lem5318895 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318896 : term401 = term402.
Proof. exact (@lem5318895 (NUMERAL 0) term389). Qed.
Lemma lem5318897 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318898 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318899 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318898 h1) (fun h1 : term402 = True => @lem5318897)). Qed.
Lemma lem5318900 : term402 = True.
Proof. exact (EQ_MP (@lem5318899) (@lem5318897)). Qed.
Lemma lem5318901 : term401 = True.
Proof. exact (TRANS (@lem5318896) (@lem5318900)). Qed.
Lemma lem5318902 : term458 = True.
Proof. exact (TRANS (@lem5318893) (@lem5318901)). Qed.
Lemma lem5318903 : term455 = True.
Proof. exact (TRANS (@lem5318879) (@lem5318902)). Qed.
Lemma lem5318904 : term401 = True.
Proof. exact (TRANS (@lem5318856) (@lem5318903)). Qed.
Lemma lem5318905 : term449 = True.
Proof. exact (TRANS (@lem5318847) (@lem5318904)). Qed.
Lemma lem5318906 : True = term449.
Proof. exact (SYM (@lem5318905)). Qed.
Lemma lem5318907 : term449.
Proof. exact (EQ_MP (@lem5318906) (@lem0)). Qed.
Lemma lem5318908 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term680 c x0.
Proof. exact (conj (@lem5318907) (@lem5318844 s c l x0 h1)). Qed.
Lemma lem5318910 (x : real) (y : real) : term477 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5318911 (c : real) (x0 : real) : term681 c x0.
Proof. exact (@lem5318910 term394 (term356 c x0)). Qed.
Lemma lem5318912 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term682 c x0.
Proof. exact (@lem5318911 c x0 (@lem5318908 s c l x0 h1)). Qed.
Lemma lem5318913 (c : real) (x0 : real) : (term683 c x0) = (term356 c x0).
Proof. exact (@lem1982733 (term356 c x0)). Qed.
Lemma lem5318914 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5318915 (c : real) (x0 : real) : (term684 c x0) = (term359 c x0).
Proof. exact (MK_COMB (@lem5318914) (@lem5318913 c x0)). Qed.
Lemma lem5318916 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5318917 (c : real) (x0 : real) : (term682 c x0) = (term361 c x0).
Proof. exact (MK_COMB (@lem5318915 c x0) (@lem5318916)). Qed.
Lemma lem5318918 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term361 c x0.
Proof. exact (EQ_MP (@lem5318917 c x0) (@lem5318912 s c l x0 h1)). Qed.
Lemma lem5318919 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term685 c x0.
Proof. exact (conj (@lem5318918 s c l x0 h1) (@lem5318396 s c l x0 h1)). Qed.
Lemma lem5318921 (x : real) (y : real) : term501 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5318922 (c : real) (x0 : real) : term686 c x0.
Proof. exact (@lem5318921 (term356 c x0) (term355 c x0)). Qed.
Lemma lem5318923 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term687 c x0.
Proof. exact (@lem5318922 c x0 (@lem5318919 s c l x0 h1)). Qed.
Lemma lem5318924 (c : real) (x0 : real) : (term688 c x0) = (term689 c x0).
Proof. exact (@lem1982753 (term357 c) c x0 (term357 x0)). Qed.
Lemma lem5318925 (c : real) : (term690 c) = (term691 c).
Proof. exact (@lem1982713 term385 c). Qed.
Lemma lem5318927 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5318928 : term394 = term451.
Proof. exact (@lem5318927 term389). Qed.
Lemma lem5318930 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5318931 : term385 = term388.
Proof. exact (@lem5318930 term389). Qed.
Lemma lem5318932 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318933 : term692 = term693.
Proof. exact (MK_COMB (@lem5318932) (@lem5318931)). Qed.
Lemma lem5318934 : term694 = term695.
Proof. exact (MK_COMB (@lem5318933) (@lem5318928)). Qed.
Lemma lem5318935 : term696.
Proof. exact (@lem1981473 term385 term394 term394 term394 term360 term394). Qed.
Lemma lem5318937 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318938 : term401 = term402.
Proof. exact (@lem5318937 (NUMERAL 0) term389). Qed.
Lemma lem5318939 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318940 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318941 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318940 h1) (fun h1 : term402 = True => @lem5318939)). Qed.
Lemma lem5318942 : term402 = True.
Proof. exact (EQ_MP (@lem5318941) (@lem5318939)). Qed.
Lemma lem5318943 : term401 = True.
Proof. exact (TRANS (@lem5318938) (@lem5318942)). Qed.
Lemma lem5318944 : True = term401.
Proof. exact (SYM (@lem5318943)). Qed.
Lemma lem5318945 : term401.
Proof. exact (EQ_MP (@lem5318944) (@lem0)). Qed.
Lemma lem5318946 : term697.
Proof. exact (@lem5318935 (@lem5318945)). Qed.
Lemma lem5318948 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318949 : term401 = term402.
Proof. exact (@lem5318948 (NUMERAL 0) term389). Qed.
Lemma lem5318950 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318951 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318952 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318951 h1) (fun h1 : term402 = True => @lem5318950)). Qed.
Lemma lem5318953 : term402 = True.
Proof. exact (EQ_MP (@lem5318952) (@lem5318950)). Qed.
Lemma lem5318954 : term401 = True.
Proof. exact (TRANS (@lem5318949) (@lem5318953)). Qed.
Lemma lem5318955 : True = term401.
Proof. exact (SYM (@lem5318954)). Qed.
Lemma lem5318956 : term401.
Proof. exact (EQ_MP (@lem5318955) (@lem0)). Qed.
Lemma lem5318957 : term698.
Proof. exact (@lem5318946 (@lem5318956)). Qed.
Lemma lem5318959 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5318960 : term401 = term402.
Proof. exact (@lem5318959 (NUMERAL 0) term389). Qed.
Lemma lem5318961 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5318962 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5318963 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5318962 h1) (fun h1 : term402 = True => @lem5318961)). Qed.
Lemma lem5318964 : term402 = True.
Proof. exact (EQ_MP (@lem5318963) (@lem5318961)). Qed.
Lemma lem5318965 : term401 = True.
Proof. exact (TRANS (@lem5318960) (@lem5318964)). Qed.
Lemma lem5318966 : True = term401.
Proof. exact (SYM (@lem5318965)). Qed.
Lemma lem5318967 : term401.
Proof. exact (EQ_MP (@lem5318966) (@lem0)). Qed.
Lemma lem5318968 : term699.
Proof. exact (@lem5318957 (@lem5318967)). Qed.
Lemma lem5318970 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5318971 : term416 = term417.
Proof. exact (@lem5318970 term389 term389). Qed.
Lemma lem5318972 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318973 : term419 = term389.
Proof. exact (EQ_MP (@lem5318972) (@lem940073)). Qed.
Lemma lem5318974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318975 : term417 = term394.
Proof. exact (MK_COMB (@lem5318974) (@lem5318973)). Qed.
Lemma lem5318976 : term416 = term394.
Proof. exact (TRANS (@lem5318971) (@lem5318975)). Qed.
Lemma lem5318978 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5318979 : term611 = term490.
Proof. exact (@lem5318978 term389 term389). Qed.
Lemma lem5318980 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5318981 : term419 = term389.
Proof. exact (EQ_MP (@lem5318980) (@lem940073)). Qed.
Lemma lem5318982 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5318983 : term417 = term394.
Proof. exact (MK_COMB (@lem5318982) (@lem5318981)). Qed.
Lemma lem5318984 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5318985 : term490 = term385.
Proof. exact (MK_COMB (@lem5318984) (@lem5318983)). Qed.
Lemma lem5318986 : term611 = term385.
Proof. exact (TRANS (@lem5318979) (@lem5318985)). Qed.
Lemma lem5318987 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5318988 : term700 = term692.
Proof. exact (MK_COMB (@lem5318987) (@lem5318986)). Qed.
Lemma lem5318989 : term701 = term694.
Proof. exact (MK_COMB (@lem5318988) (@lem5318976)). Qed.
Lemma lem5318991 (m : nat) : (term517 m) = term360.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5318992 : term694 = term360.
Proof. exact (@lem5318991 term389). Qed.
Lemma lem5318993 : term701 = term360.
Proof. exact (TRANS (@lem5318989) (@lem5318992)). Qed.
Lemma lem5318994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5318995 : term702 = term519.
Proof. exact (MK_COMB (@lem5318994) (@lem5318993)). Qed.
Lemma lem5318996 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem5318997 : term703 = term460.
Proof. exact (MK_COMB (@lem5318995) (@lem5318996)). Qed.
Lemma lem5318999 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5319000 : term460 = term360.
Proof. exact (@lem5318999 term389). Qed.
Lemma lem5319001 : term703 = term360.
Proof. exact (TRANS (@lem5318997) (@lem5319000)). Qed.
Lemma lem5319003 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319004 : term416 = term417.
Proof. exact (@lem5319003 term389 term389). Qed.
Lemma lem5319005 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319006 : term419 = term389.
Proof. exact (EQ_MP (@lem5319005) (@lem940073)). Qed.
Lemma lem5319007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319008 : term417 = term394.
Proof. exact (MK_COMB (@lem5319007) (@lem5319006)). Qed.
Lemma lem5319009 : term416 = term394.
Proof. exact (TRANS (@lem5319004) (@lem5319008)). Qed.
Lemma lem5319010 : term519 = term519.
Proof. exact (eq_refl term519). Qed.
Lemma lem5319011 : term704 = term460.
Proof. exact (MK_COMB (@lem5319010) (@lem5319009)). Qed.
Lemma lem5319013 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5319014 : term460 = term360.
Proof. exact (@lem5319013 term389). Qed.
Lemma lem5319015 : term704 = term360.
Proof. exact (TRANS (@lem5319011) (@lem5319014)). Qed.
Lemma lem5319016 : term360 = term704.
Proof. exact (SYM (@lem5319015)). Qed.
Lemma lem5319017 : term703 = term704.
Proof. exact (TRANS (@lem5319001) (@lem5319016)). Qed.
Lemma lem5319018 : term695 = term452.
Proof. exact (@lem5318968 (@lem5319017)). Qed.
Lemma lem5319019 : term694 = term452.
Proof. exact (TRANS (@lem5318934) (@lem5319018)). Qed.
Lemma lem5319021 (x : real) : (term531 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5319022 : term452 = term360.
Proof. exact (@lem5319021 term360). Qed.
Lemma lem5319023 : term694 = term360.
Proof. exact (TRANS (@lem5319019) (@lem5319022)). Qed.
Lemma lem5319024 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319025 : term705 = term519.
Proof. exact (MK_COMB (@lem5319024) (@lem5319023)). Qed.
Lemma lem5319026 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5319027 (c : real) : (term691 c) = (term533 c).
Proof. exact (MK_COMB (@lem5319025) (@lem5319026 c)). Qed.
Lemma lem5319028 (c : real) : (term690 c) = (term533 c).
Proof. exact (TRANS (@lem5318925 c) (@lem5319027 c)). Qed.
Lemma lem5319029 (c : real) : (term533 c) = term360.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5319030 (c : real) : (term690 c) = term360.
Proof. exact (TRANS (@lem5319028 c) (@lem5319029 c)). Qed.
Lemma lem5319031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5319032 (c : real) : (term706 c) = term535.
Proof. exact (MK_COMB (@lem5319031) (@lem5319030 c)). Qed.
Lemma lem5319033 (x0 : real) : (term707 x0) = (term691 x0).
Proof. exact (@lem1982715 term385 x0). Qed.
Lemma lem5319035 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5319036 : term394 = term451.
Proof. exact (@lem5319035 term389). Qed.
Lemma lem5319038 (x : nat) : (term386 x) = (term387 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5319039 : term385 = term388.
Proof. exact (@lem5319038 term389). Qed.
Lemma lem5319040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5319041 : term692 = term693.
Proof. exact (MK_COMB (@lem5319040) (@lem5319039)). Qed.
Lemma lem5319042 : term694 = term695.
Proof. exact (MK_COMB (@lem5319041) (@lem5319036)). Qed.
Lemma lem5319043 : term696.
Proof. exact (@lem1981473 term385 term394 term394 term394 term360 term394). Qed.
Lemma lem5319045 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319046 : term401 = term402.
Proof. exact (@lem5319045 (NUMERAL 0) term389). Qed.
Lemma lem5319047 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319048 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319049 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5319048 h1) (fun h1 : term402 = True => @lem5319047)). Qed.
Lemma lem5319050 : term402 = True.
Proof. exact (EQ_MP (@lem5319049) (@lem5319047)). Qed.
Lemma lem5319051 : term401 = True.
Proof. exact (TRANS (@lem5319046) (@lem5319050)). Qed.
Lemma lem5319052 : True = term401.
Proof. exact (SYM (@lem5319051)). Qed.
Lemma lem5319053 : term401.
Proof. exact (EQ_MP (@lem5319052) (@lem0)). Qed.
Lemma lem5319054 : term697.
Proof. exact (@lem5319043 (@lem5319053)). Qed.
Lemma lem5319056 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319057 : term401 = term402.
Proof. exact (@lem5319056 (NUMERAL 0) term389). Qed.
Lemma lem5319058 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319059 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319060 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5319059 h1) (fun h1 : term402 = True => @lem5319058)). Qed.
Lemma lem5319061 : term402 = True.
Proof. exact (EQ_MP (@lem5319060) (@lem5319058)). Qed.
Lemma lem5319062 : term401 = True.
Proof. exact (TRANS (@lem5319057) (@lem5319061)). Qed.
Lemma lem5319063 : True = term401.
Proof. exact (SYM (@lem5319062)). Qed.
Lemma lem5319064 : term401.
Proof. exact (EQ_MP (@lem5319063) (@lem0)). Qed.
Lemma lem5319065 : term698.
Proof. exact (@lem5319054 (@lem5319064)). Qed.
Lemma lem5319067 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319068 : term401 = term402.
Proof. exact (@lem5319067 (NUMERAL 0) term389). Qed.
Lemma lem5319069 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319070 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319071 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5319070 h1) (fun h1 : term402 = True => @lem5319069)). Qed.
Lemma lem5319072 : term402 = True.
Proof. exact (EQ_MP (@lem5319071) (@lem5319069)). Qed.
Lemma lem5319073 : term401 = True.
Proof. exact (TRANS (@lem5319068) (@lem5319072)). Qed.
Lemma lem5319074 : True = term401.
Proof. exact (SYM (@lem5319073)). Qed.
Lemma lem5319075 : term401.
Proof. exact (EQ_MP (@lem5319074) (@lem0)). Qed.
Lemma lem5319076 : term699.
Proof. exact (@lem5319065 (@lem5319075)). Qed.
Lemma lem5319078 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319079 : term416 = term417.
Proof. exact (@lem5319078 term389 term389). Qed.
Lemma lem5319080 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319081 : term419 = term389.
Proof. exact (EQ_MP (@lem5319080) (@lem940073)). Qed.
Lemma lem5319082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319083 : term417 = term394.
Proof. exact (MK_COMB (@lem5319082) (@lem5319081)). Qed.
Lemma lem5319084 : term416 = term394.
Proof. exact (TRANS (@lem5319079) (@lem5319083)). Qed.
Lemma lem5319086 (m : nat) (n : nat) : (term406 m n) = (term407 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319087 : term611 = term490.
Proof. exact (@lem5319086 term389 term389). Qed.
Lemma lem5319088 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319089 : term419 = term389.
Proof. exact (EQ_MP (@lem5319088) (@lem940073)). Qed.
Lemma lem5319090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319091 : term417 = term394.
Proof. exact (MK_COMB (@lem5319090) (@lem5319089)). Qed.
Lemma lem5319092 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319093 : term490 = term385.
Proof. exact (MK_COMB (@lem5319092) (@lem5319091)). Qed.
Lemma lem5319094 : term611 = term385.
Proof. exact (TRANS (@lem5319087) (@lem5319093)). Qed.
Lemma lem5319095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5319096 : term700 = term692.
Proof. exact (MK_COMB (@lem5319095) (@lem5319094)). Qed.
Lemma lem5319097 : term701 = term694.
Proof. exact (MK_COMB (@lem5319096) (@lem5319084)). Qed.
Lemma lem5319099 (m : nat) : (term517 m) = term360.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5319100 : term694 = term360.
Proof. exact (@lem5319099 term389). Qed.
Lemma lem5319101 : term701 = term360.
Proof. exact (TRANS (@lem5319097) (@lem5319100)). Qed.
Lemma lem5319102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319103 : term702 = term519.
Proof. exact (MK_COMB (@lem5319102) (@lem5319101)). Qed.
Lemma lem5319104 : term394 = term394.
Proof. exact (eq_refl term394). Qed.
Lemma lem5319105 : term703 = term460.
Proof. exact (MK_COMB (@lem5319103) (@lem5319104)). Qed.
Lemma lem5319107 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5319108 : term460 = term360.
Proof. exact (@lem5319107 term389). Qed.
Lemma lem5319109 : term703 = term360.
Proof. exact (TRANS (@lem5319105) (@lem5319108)). Qed.
Lemma lem5319111 (m : nat) (n : nat) : (term414 m n) = (term415 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319112 : term416 = term417.
Proof. exact (@lem5319111 term389 term389). Qed.
Lemma lem5319113 : (term418 = (BIT1 0)) = (term419 = term389).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319114 : term419 = term389.
Proof. exact (EQ_MP (@lem5319113) (@lem940073)). Qed.
Lemma lem5319115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319116 : term417 = term394.
Proof. exact (MK_COMB (@lem5319115) (@lem5319114)). Qed.
Lemma lem5319117 : term416 = term394.
Proof. exact (TRANS (@lem5319112) (@lem5319116)). Qed.
Lemma lem5319118 : term519 = term519.
Proof. exact (eq_refl term519). Qed.
Lemma lem5319119 : term704 = term460.
Proof. exact (MK_COMB (@lem5319118) (@lem5319117)). Qed.
Lemma lem5319121 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5319122 : term460 = term360.
Proof. exact (@lem5319121 term389). Qed.
Lemma lem5319123 : term704 = term360.
Proof. exact (TRANS (@lem5319119) (@lem5319122)). Qed.
Lemma lem5319124 : term360 = term704.
Proof. exact (SYM (@lem5319123)). Qed.
Lemma lem5319125 : term703 = term704.
Proof. exact (TRANS (@lem5319109) (@lem5319124)). Qed.
Lemma lem5319126 : term695 = term452.
Proof. exact (@lem5319076 (@lem5319125)). Qed.
Lemma lem5319127 : term694 = term452.
Proof. exact (TRANS (@lem5319042) (@lem5319126)). Qed.
Lemma lem5319129 (x : real) : (term531 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5319130 : term452 = term360.
Proof. exact (@lem5319129 term360). Qed.
Lemma lem5319131 : term694 = term360.
Proof. exact (TRANS (@lem5319127) (@lem5319130)). Qed.
Lemma lem5319132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319133 : term705 = term519.
Proof. exact (MK_COMB (@lem5319132) (@lem5319131)). Qed.
Lemma lem5319134 (x0 : real) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem5319135 (x0 : real) : (term691 x0) = (term533 x0).
Proof. exact (MK_COMB (@lem5319133) (@lem5319134 x0)). Qed.
Lemma lem5319136 (x0 : real) : (term707 x0) = (term533 x0).
Proof. exact (TRANS (@lem5319033 x0) (@lem5319135 x0)). Qed.
Lemma lem5319137 (x0 : real) : (term533 x0) = term360.
Proof. exact (@lem1982719 x0). Qed.
Lemma lem5319138 (x0 : real) : (term707 x0) = term360.
Proof. exact (TRANS (@lem5319136 x0) (@lem5319137 x0)). Qed.
Lemma lem5319139 (c : real) (x0 : real) : (term689 c x0) = term551.
Proof. exact (MK_COMB (@lem5319032 c) (@lem5319138 x0)). Qed.
Lemma lem5319140 (c : real) (x0 : real) : (term688 c x0) = term551.
Proof. exact (TRANS (@lem5318924 c x0) (@lem5319139 c x0)). Qed.
Lemma lem5319141 : term551 = term360.
Proof. exact (@lem1982721 term360). Qed.
Lemma lem5319142 (c : real) (x0 : real) : (term688 c x0) = term360.
Proof. exact (TRANS (@lem5319140 c x0) (@lem5319141)). Qed.
Lemma lem5319143 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5319144 (c : real) (x0 : real) : (term708 c x0) = term553.
Proof. exact (MK_COMB (@lem5319143) (@lem5319142 c x0)). Qed.
Lemma lem5319145 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem5319146 (c : real) (x0 : real) : (term687 c x0) = term554.
Proof. exact (MK_COMB (@lem5319144 c x0) (@lem5319145)). Qed.
Lemma lem5319147 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term554.
Proof. exact (EQ_MP (@lem5319146 c x0) (@lem5318923 s c l x0 h1)). Qed.
Lemma lem5319149 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5319150 : term554 = term555.
Proof. exact (@lem5319149 term360 term360). Qed.
Lemma lem5319152 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5319153 : term360 = term452.
Proof. exact (@lem5319152 (NUMERAL 0)). Qed.
Lemma lem5319155 (x : nat) : (real_of_num x) = (term450 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5319156 : term360 = term452.
Proof. exact (@lem5319155 (NUMERAL 0)). Qed.
Lemma lem5319157 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5319158 : term453 = term454.
Proof. exact (MK_COMB (@lem5319157) (@lem5319156)). Qed.
Lemma lem5319159 : term555 = term556.
Proof. exact (MK_COMB (@lem5319158) (@lem5319153)). Qed.
Lemma lem5319160 : term557.
Proof. exact (@lem1980255 term360 term394 term360 term394). Qed.
Lemma lem5319162 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319163 : term401 = term402.
Proof. exact (@lem5319162 (NUMERAL 0) term389). Qed.
Lemma lem5319164 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319165 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319166 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5319165 h1) (fun h1 : term402 = True => @lem5319164)). Qed.
Lemma lem5319167 : term402 = True.
Proof. exact (EQ_MP (@lem5319166) (@lem5319164)). Qed.
Lemma lem5319168 : term401 = True.
Proof. exact (TRANS (@lem5319163) (@lem5319167)). Qed.
Lemma lem5319169 : True = term401.
Proof. exact (SYM (@lem5319168)). Qed.
Lemma lem5319170 : term401.
Proof. exact (EQ_MP (@lem5319169) (@lem0)). Qed.
Lemma lem5319171 : term558.
Proof. exact (@lem5319160 (@lem5319170)). Qed.
Lemma lem5319173 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319174 : term401 = term402.
Proof. exact (@lem5319173 (NUMERAL 0) term389). Qed.
Lemma lem5319175 : term403 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319176 (h1 : term403 = (BIT1 0)) : term402 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319177 : (term403 = (BIT1 0)) = (term402 = True).
Proof. exact (prop_ext (fun h1 : term403 = (BIT1 0) => @lem5319176 h1) (fun h1 : term402 = True => @lem5319175)). Qed.
Lemma lem5319178 : term402 = True.
Proof. exact (EQ_MP (@lem5319177) (@lem5319175)). Qed.
Lemma lem5319179 : term401 = True.
Proof. exact (TRANS (@lem5319174) (@lem5319178)). Qed.
Lemma lem5319180 : True = term401.
Proof. exact (SYM (@lem5319179)). Qed.
Lemma lem5319181 : term401.
Proof. exact (EQ_MP (@lem5319180) (@lem0)). Qed.
Lemma lem5319182 : term556 = term559.
Proof. exact (@lem5319171 (@lem5319181)). Qed.
Lemma lem5319184 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5319185 : term460 = term360.
Proof. exact (@lem5319184 term389). Qed.
Lemma lem5319187 (x : nat) : (term459 x) = term360.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5319188 : term460 = term360.
Proof. exact (@lem5319187 term389). Qed.
Lemma lem5319189 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5319190 : term461 = term453.
Proof. exact (MK_COMB (@lem5319189) (@lem5319188)). Qed.
Lemma lem5319191 : term559 = term555.
Proof. exact (MK_COMB (@lem5319190) (@lem5319185)). Qed.
Lemma lem5319193 (m : nat) (n : nat) : (term395 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319194 : term555 = term560.
Proof. exact (@lem5319193 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5319195 : term560 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5319196 : term555 = False.
Proof. exact (TRANS (@lem5319194) (@lem5319195)). Qed.
Lemma lem5319197 : term559 = False.
Proof. exact (TRANS (@lem5319191) (@lem5319196)). Qed.
Lemma lem5319198 : term556 = False.
Proof. exact (TRANS (@lem5319182) (@lem5319197)). Qed.
Lemma lem5319199 : term555 = False.
Proof. exact (TRANS (@lem5319159) (@lem5319198)). Qed.
Lemma lem5319200 : term554 = False.
Proof. exact (TRANS (@lem5319150) (@lem5319199)). Qed.
Lemma lem5319201 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : False.
Proof. exact (EQ_MP (@lem5319200) (@lem5319147 s c l x0 h1)). Qed.
Lemma lem5319203 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : term628 s c l x0.
Proof. exact (h1). Qed.
Lemma lem5319204 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : (term628 s c l x0) = False.
Proof. exact (prop_ext (fun h2 : term628 s c l x0 => @lem5319201 s c l x0 h1) (fun h2 : False => @lem5319203 s c l x0 h1)). Qed.
Lemma lem5319205 (s : real -> Prop) (c : real) (l : real) (x0 : real) (h1 : term628 s c l x0) : False.
Proof. exact (EQ_MP (@lem5319204 s c l x0 h1) (@lem5319203 s c l x0 h1)). Qed.
Lemma lem5319206 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term579 s l c x0) : term579 s l c x0.
Proof. exact (h1). Qed.
Lemma lem5319207 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term579 s l c x0) : term628 s c l x0.
Proof. exact (EQ_MP (@lem5318310 s c l x0) (@lem5319206 s l c x0 h1)). Qed.
Lemma lem5319208 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term579 s l c x0) : (term628 s c l x0) = False.
Proof. exact (prop_ext (fun h2 : term628 s c l x0 => @lem5319205 s c l x0 h2) (fun h2 : False => @lem5319207 s l c x0 h1)). Qed.
Lemma lem5319209 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term579 s l c x0) : False.
Proof. exact (EQ_MP (@lem5319208 s l c x0 h1) (@lem5319207 s l c x0 h1)). Qed.
Lemma lem5319210 (s : real -> Prop) (l : real) (c : real) (x0 : real) : term709 s l c x0.
Proof. exact (fun h0 : term579 s l c x0 => @lem5319209 s l c x0 h0). Qed.
Lemma lem5319211 (s : real -> Prop) (l : real) (c : real) (x0 : real) : term710 s l c x0.
Proof. exact (@lem1386578 (term577 s l c x0)). Qed.
Lemma lem5319214 (s : real -> Prop) (l : real) (c : real) (x0 : real) : term577 s l c x0.
Proof. exact (@lem5319211 s l c x0 (@lem5319210 s l c x0)). Qed.
Lemma lem5319215 (l : real) (c : real) (x0 : real) (s : real -> Prop) (h1 : term22 s) : term574 s l c x0.
Proof. exact (@lem5319214 s l c x0 (@lem5317177 s h1)). Qed.
Lemma lem5319216 (x0 : real) (s : real -> Prop) (c : real) (l : real) (h1 : term22 s) (h2 : real_lt c l) : term572 s l c x0.
Proof. exact (@lem5319215 l c x0 s h1 (@lem5317230 c l h2)). Qed.
Lemma lem5319217 (x0 : real) (s : real -> Prop) (c : real) (l : real) (h1 : term22 s) (h2 : @IN real x0 s) (h3 : real_lt c l) : term569 l c x0.
Proof. exact (@lem5319216 x0 s c l h1 h3 (@lem5318001 x0 s h2)). Qed.
Lemma lem5319218 (x0 : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt c l) : term566 l c x0.
Proof. exact (@lem5319217 x0 s c l h2 h3 h4 (@lem5318008 c x0 s h1 h3)). Qed.
Lemma lem5319219 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term564 s l c x0) : term565 l c x0.
Proof. exact (proj2 (@lem5317999 s l c x0 h1)). Qed.
Lemma lem5319220 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term564 s l c x0) : @IN real x0 s.
Proof. exact (proj1 (@lem5317999 s l c x0 h1)). Qed.
Lemma lem5319221 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt c l) (h5 : term565 l c x0) : False.
Proof. exact (@lem5319218 x0 s c l h1 h2 h3 h4 (@lem5318000 l c x0 h5)). Qed.
Lemma lem5319222 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt c l) (h5 : term565 l c x0) : (@IN real x0 s) = False.
Proof. exact (prop_ext (fun h6 : @IN real x0 s => @lem5319221 s l c x0 h1 h2 h3 h4 h5) (fun h6 : False => @lem5318001 x0 s h3)). Qed.
Lemma lem5319223 (s : real -> Prop) (l : real) (c : real) (x0 : real) (h1 : term25 s c) (h2 : term22 s) (h3 : @IN real x0 s) (h4 : real_lt c l) (h5 : term565 l c x0) : False.
Proof. exact (EQ_MP (@lem5319222 s l c x0 h1 h2 h3 h4 h5) (@lem5318001 x0 s h3)). Qed.
Lemma lem5319224 (x0 : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term564 s l c x0) (h4 : @IN real x0 s) (h5 : real_lt c l) : (term565 l c x0) = False.
Proof. exact (prop_ext (fun h6 : term565 l c x0 => @lem5319223 s l c x0 h1 h2 h4 h5 h6) (fun h6 : False => @lem5319219 s l c x0 h3)). Qed.
Lemma lem5319225 (x0 : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term564 s l c x0) (h4 : @IN real x0 s) (h5 : real_lt c l) : False.
Proof. exact (EQ_MP (@lem5319224 x0 s c l h1 h2 h3 h4 h5) (@lem5319219 s l c x0 h3)). Qed.
Lemma lem5319226 (s : real -> Prop) (x0 : real) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term564 s l c x0) (h4 : real_lt c l) : (@IN real x0 s) = False.
Proof. exact (prop_ext (fun h5 : @IN real x0 s => @lem5319225 x0 s c l h1 h2 h3 h5 h4) (fun h5 : False => @lem5319220 s l c x0 h3)). Qed.
Lemma lem5319227 (s : real -> Prop) (x0 : real) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : term564 s l c x0) (h4 : real_lt c l) : False.
Proof. exact (EQ_MP (@lem5319226 s x0 c l h1 h2 h3 h4) (@lem5319220 s l c x0 h3)). Qed.
Lemma lem5319228 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term346 s l c) (h3 : term22 s) (h4 : real_lt c l) : False.
Proof. exact (ex_elim (@lem5317998 s l c h2) (fun x0 : real => fun h0 : term711 s l c x0 => @lem5319227 s x0 c l h1 h3 h0 h4)). Qed.
Lemma lem5319229 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : real_lt c l) : term712 s l c.
Proof. exact (fun h0 : term346 s l c => @lem5319228 s c l h1 h0 h2 h3). Qed.
Lemma lem5319230 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : real_lt c l) : term713 s l c.
Proof. exact (conj (@lem5317997 s c l h2 h3) (@lem5319229 s c l h1 h2 h3)). Qed.
Lemma lem5319231 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term22 s) (h3 : real_lt c l) : term714 s l c.
Proof. exact (@lem5317236 s l c (@lem5319230 s c l h1 h2 h3)). Qed.
Lemma lem5319232 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) (h4 : real_lt c l) : False.
Proof. exact (@lem5319231 s c l h1 h3 h4 (@lem5317233 c l s h2)). Qed.
Lemma lem5319233 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) (h4 : real_lt c l) : (real_lt c l) = False.
Proof. exact (prop_ext (fun h5 : real_lt c l => @lem5319232 s c l h1 h2 h3 h4) (fun h5 : False => @lem5317230 c l h4)). Qed.
Lemma lem5319234 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) (h4 : real_lt c l) : False.
Proof. exact (EQ_MP (@lem5319233 s c l h1 h2 h3 h4) (@lem5317230 c l h4)). Qed.
Lemma lem5319235 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : term715 c l.
Proof. exact (fun h0 : real_lt c l => @lem5319234 s c l h1 h2 h3 h0). Qed.
Lemma lem5319236 (c : real) (l : real) : (term715 c l) = (term0 c l).
Proof. exact (@lem69 (real_lt c l)). Qed.
Lemma lem5319237 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : term0 c l.
Proof. exact (EQ_MP (@lem5319236 c l) (@lem5319235 c l s h1 h2 h3)). Qed.
Lemma lem5319238 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : real_le l c.
Proof. exact (EQ_MP (@lem5317229 l c) (@lem5319237 c l s h1 h2 h3)). Qed.
Lemma lem5319239 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : (term25 s c) = (real_le l c).
Proof. exact (prop_ext (fun h4 : term25 s c => @lem5319238 c l s h1 h2 h3) (fun h4 : real_le l c => @lem5317225 s c h1)). Qed.
Lemma lem5319240 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s c) (h2 : term118 l s) (h3 : term22 s) : real_le l c.
Proof. exact (EQ_MP (@lem5319239 c l s h1 h2 h3) (@lem5317225 s c h1)). Qed.
Lemma lem5319241 (c : real) (l : real) (s : real -> Prop) (h1 : term118 l s) (h2 : term22 s) : term716 s l c.
Proof. exact (fun h0 : term25 s c => @lem5319240 c l s h0 h1 h2). Qed.
Lemma lem5319242 (l : real) (c : real) (h1 : real_le l c) : real_le l c.
Proof. exact (h1). Qed.
Lemma lem5319245 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5319246 (h1 : term717) : term717.
Proof. exact (h1). Qed.
Lemma lem5319247 (x : real) (h1 : term717) : term718 x.
Proof. exact (@lem5319246 h1 x). Qed.
Lemma lem5319248 (x : real) : (term718 x) = (term719 x).
Proof. exact (eq_refl (term718 x)). Qed.
Lemma lem5319249 (x : real) (h1 : term717) : term719 x.
Proof. exact (EQ_MP (@lem5319248 x) (@lem5319247 x h1)). Qed.
Lemma lem5319250 (x : real) (y : real) (h1 : term717) : term720 x y.
Proof. exact (@lem5319249 x h1 y). Qed.
Lemma lem5319251 (y : real) (x : real) : (term720 x y) = (term721 y x).
Proof. exact (eq_refl (term720 x y)). Qed.
Lemma lem5319252 (y : real) (x : real) (h1 : term717) : term721 y x.
Proof. exact (EQ_MP (@lem5319251 y x) (@lem5319250 x y h1)). Qed.
Lemma lem5319253 (y : real) (x : real) (z : real) (h1 : term717) : term722 y x z.
Proof. exact (@lem5319252 y x h1 z). Qed.
Lemma lem5319254 (y : real) (x : real) (z : real) : (term722 y x z) = (term723 y x z).
Proof. exact (eq_refl (term722 y x z)). Qed.
Lemma lem5319255 (y : real) (x : real) (z : real) (h1 : term717) : term723 y x z.
Proof. exact (EQ_MP (@lem5319254 y x z) (@lem5319253 y x z h1)). Qed.
Lemma lem5319256 (x : real) (y : real) (z : real) (h1 : term724 x y z) : term724 x y z.
Proof. exact (h1). Qed.
Lemma lem5319257 (x : real) (y : real) (z : real) (h1 : term717) (h2 : term724 x y z) : real_le x z.
Proof. exact (@lem5319255 y x z h1 (@lem5319256 x y z h2)). Qed.
Lemma lem5319258 (x : real) (y : real) (z : real) (h1 : term724 x y z) : term725 x z.
Proof. exact (fun h0 : term717 => @lem5319257 x y z h0 h1). Qed.
Lemma lem5319259 (x : real) (z : real) (h1 : term726 x z) : term726 x z.
Proof. exact (h1). Qed.
Lemma lem5319260 (x : real) (z : real) (h1 : term726 x z) : term725 x z.
Proof. exact (ex_elim (@lem5319259 x z h1) (fun y : real => fun h0 : term727 x z y => @lem5319258 x y z h0)). Qed.
Lemma lem5319261 (h1 : term717) : term717.
Proof. exact (h1). Qed.
Lemma lem5319262 (x : real) (z : real) (h1 : term717) (h2 : term726 x z) : real_le x z.
Proof. exact (@lem5319260 x z h2 (@lem5319261 h1)). Qed.
Lemma lem5319263 (x : real) (z : real) (h1 : term717) : term728 x z.
Proof. exact (fun h0 : term726 x z => @lem5319262 x z h1 h0). Qed.
Lemma lem5319264 (x : real) (h1 : term717) : term729 x.
Proof. exact (fun z : real => @lem5319263 x z h1). Qed.
Lemma lem5319265 (h1 : term717) : term730.
Proof. exact (fun x : real => @lem5319264 x h1). Qed.
Lemma lem5319266 : term731.
Proof. exact (fun h0 : term717 => @lem5319265 h0). Qed.
Lemma lem5319267 : term730.
Proof. exact (@lem5319266 (@lem1339577)). Qed.
Lemma lem5319268 (x : real) : term732 x.
Proof. exact (@lem5319267 x). Qed.
Lemma lem5319269 (x : real) : (term732 x) = (term729 x).
Proof. exact (eq_refl (term732 x)). Qed.
Lemma lem5319270 (x : real) : term729 x.
Proof. exact (EQ_MP (@lem5319269 x) (@lem5319268 x)). Qed.
Lemma lem5319271 (x : real) (z : real) : term733 x z.
Proof. exact (@lem5319270 x z). Qed.
Lemma lem5319272 (x : real) (z : real) : (term733 x z) = (term728 x z).
Proof. exact (eq_refl (term733 x z)). Qed.
Lemma lem5319275 (x : real) (z : real) : term728 x z.
Proof. exact (EQ_MP (@lem5319272 x z) (@lem5319271 x z)). Qed.
Lemma lem5319276 (x : real) (c : real) : term728 x c.
Proof. exact (@lem5319275 x c). Qed.
Lemma lem5319290 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term61 s l x.
Proof. exact (@lem5317179 s l h1 x). Qed.
Lemma lem5319291 (s : real -> Prop) (x : real) (l : real) : (term61 s l x) = (term54 s x l).
Proof. exact (eq_refl (term61 s l x)). Qed.
Lemma lem5319292 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term54 s x l.
Proof. exact (EQ_MP (@lem5319291 s x l) (@lem5319290 x s l h1)). Qed.
Lemma lem5319293 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5319294 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : real_le x l.
Proof. exact (@lem5319292 x s l h1 (@lem5319293 x s h2)). Qed.
Lemma lem5319295 (x : real) (l : real) : (real_le x l) = ((real_le x l) = True).
Proof. exact (@lem7 (real_le x l)). Qed.
Lemma lem5319296 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le x l) = True.
Proof. exact (EQ_MP (@lem5319295 x l) (@lem5319294 l x s h1 h2)). Qed.
Lemma lem5319314 (l : real) (c : real) : (real_le l c) = ((real_le l c) = True).
Proof. exact (@lem7 (real_le l c)). Qed.
Lemma lem5319316 (x : real) (s : real -> Prop) : (@IN real x s) = ((@IN real x s) = True).
Proof. exact (@lem7 (@IN real x s)). Qed.
Lemma lem5319321 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term734 s x l.
Proof. exact (fun h0 : @IN real x s => @lem5319296 l x s h1 h0). Qed.
Lemma lem5319323 (x : real) (s : real -> Prop) (h1 : @IN real x s) : (@IN real x s) = True.
Proof. exact (EQ_MP (@lem5319316 x s) (@lem5319245 x s h1)). Qed.
Lemma lem5319324 (x : real) (s : real -> Prop) (h1 : @IN real x s) : True = (@IN real x s).
Proof. exact (SYM (@lem5319323 x s h1)). Qed.
Lemma lem5319325 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (EQ_MP (@lem5319324 x s h1) (@lem0)). Qed.
Lemma lem5319326 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le x l) = True.
Proof. exact (@lem5319321 x s l h1 (@lem5319325 x s h2)). Qed.
Lemma lem5319327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5319328 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (term582 x l) = (and True).
Proof. exact (MK_COMB (@lem5319327) (@lem5319326 l x s h1 h2)). Qed.
Lemma lem5319330 (l : real) (c : real) (h1 : real_le l c) : (real_le l c) = True.
Proof. exact (EQ_MP (@lem5319314 l c) (@lem5319242 l c h1)). Qed.
Lemma lem5319331 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : (term724 x l c) = (True /\ True).
Proof. exact (MK_COMB (@lem5319328 l x s h1 h2) (@lem5319330 l c h3)). Qed.
Lemma lem5319333 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5319334 : (True /\ True) = True.
Proof. exact (@lem5319333 True). Qed.
Lemma lem5319335 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : (term724 x l c) = True.
Proof. exact (TRANS (@lem5319331 x s l c h1 h2 h3) (@lem5319334)). Qed.
Lemma lem5319336 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : True = (term724 x l c).
Proof. exact (SYM (@lem5319335 x s l c h1 h2 h3)). Qed.
Lemma lem5319337 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : term724 x l c.
Proof. exact (EQ_MP (@lem5319336 x s l c h1 h2 h3) (@lem0)). Qed.
Lemma lem5319338 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : term726 x c.
Proof. exact (ex_intro (term727 x c) l (@lem5319337 x s l c h1 h2 h3)). Qed.
Lemma lem5319339 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : real_le x c.
Proof. exact (@lem5319276 x c (@lem5319338 x s l c h1 h2 h3)). Qed.
Lemma lem5319340 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : (@IN real x s) = (real_le x c).
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5319339 x s l c h1 h2 h3) (fun h4 : real_le x c => @lem5319245 x s h2)). Qed.
Lemma lem5319341 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : real_le x c.
Proof. exact (EQ_MP (@lem5319340 x s l c h1 h2 h3) (@lem5319245 x s h2)). Qed.
Lemma lem5319342 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : term54 s x c.
Proof. exact (fun h0 : @IN real x s => @lem5319341 x s l c h1 h0 h2). Qed.
Lemma lem5319348 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : term25 s c.
Proof. exact (fun x : real => @lem5319342 x s l c h1 h2). Qed.
Lemma lem5319349 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : (real_le l c) = (term25 s c).
Proof. exact (prop_ext (fun h3 : real_le l c => @lem5319348 s l c h1 h2) (fun h3 : term25 s c => @lem5319242 l c h2)). Qed.
Lemma lem5319350 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : term25 s c.
Proof. exact (EQ_MP (@lem5319349 s l c h1 h2) (@lem5319242 l c h2)). Qed.
Lemma lem5319351 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term735 l s c.
Proof. exact (fun h0 : real_le l c => @lem5319350 s l c h1 h0). Qed.
Lemma lem5319352 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : term736 l s c.
Proof. exact (conj (@lem5319241 c l s h2 h3) (@lem5319351 c s l h1)). Qed.
Lemma lem5319353 (s : real -> Prop) (l : real) (c : real) : (term736 l s c) = ((term25 s c) = (real_le l c)).
Proof. exact (@lem32 (term25 s c) (real_le l c)). Qed.
Lemma lem5319354 (c : real) (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5319353 s l c) (@lem5319352 c l s h1 h2 h3)). Qed.
Lemma lem5319359 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : term339 s l.
Proof. exact (fun c : real => @lem5319354 c l s h1 h2 h3). Qed.
Lemma lem5319360 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : has_sup s l.
Proof. exact (EQ_MP (@lem5317224 s l) (@lem5319359 l s h1 h2 h3)). Qed.
Lemma lem5319361 (l : real) (s : real -> Prop) (h1 : term334 l s) : term333 l s.
Proof. exact (proj2 (@lem5317175 l s h1)). Qed.
Lemma lem5319362 (l : real) (s : real -> Prop) (h1 : term334 l s) : term22 s.
Proof. exact (proj1 (@lem5317175 l s h1)). Qed.
Lemma lem5319363 (l : real) (s : real -> Prop) (h1 : term333 l s) : term118 l s.
Proof. exact (proj2 (@lem5317176 l s h1)). Qed.
Lemma lem5319364 (l : real) (s : real -> Prop) (h1 : term333 l s) : term25 s l.
Proof. exact (proj1 (@lem5317176 l s h1)). Qed.
Lemma lem5319365 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : (term118 l s) = (has_sup s l).
Proof. exact (prop_ext (fun h4 : term118 l s => @lem5319360 l s h1 h2 h3) (fun h4 : has_sup s l => @lem5317178 l s h2)). Qed.
Lemma lem5319366 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319365 l s h1 h2 h3) (@lem5317178 l s h2)). Qed.
Lemma lem5319367 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : (term25 s l) = (has_sup s l).
Proof. exact (prop_ext (fun h4 : term25 s l => @lem5319366 l s h1 h2 h3) (fun h4 : has_sup s l => @lem5317179 s l h1)). Qed.
Lemma lem5319368 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term118 l s) (h3 : term22 s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319367 l s h1 h2 h3) (@lem5317179 s l h1)). Qed.
Lemma lem5319369 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term22 s) (h3 : term333 l s) : (term118 l s) = (has_sup s l).
Proof. exact (prop_ext (fun h4 : term118 l s => @lem5319368 l s h1 h4 h2) (fun h4 : has_sup s l => @lem5319363 l s h3)). Qed.
Lemma lem5319370 (l : real) (s : real -> Prop) (h1 : term25 s l) (h2 : term22 s) (h3 : term333 l s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319369 l s h1 h2 h3) (@lem5319363 l s h3)). Qed.
Lemma lem5319371 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : (term25 s l) = (has_sup s l).
Proof. exact (prop_ext (fun h3 : term25 s l => @lem5319370 l s h3 h1 h2) (fun h3 : has_sup s l => @lem5319364 l s h2)). Qed.
Lemma lem5319372 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319371 l s h1 h2) (@lem5319364 l s h2)). Qed.
Lemma lem5319373 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : (term22 s) = (has_sup s l).
Proof. exact (prop_ext (fun h3 : term22 s => @lem5319372 l s h1 h2) (fun h3 : has_sup s l => @lem5317177 s h1)). Qed.
Lemma lem5319374 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term333 l s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319373 l s h1 h2) (@lem5317177 s h1)). Qed.
Lemma lem5319375 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term334 l s) : (term333 l s) = (has_sup s l).
Proof. exact (prop_ext (fun h3 : term333 l s => @lem5319374 l s h1 h3) (fun h3 : has_sup s l => @lem5319361 l s h2)). Qed.
Lemma lem5319376 (l : real) (s : real -> Prop) (h1 : term22 s) (h2 : term334 l s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319375 l s h1 h2) (@lem5319361 l s h2)). Qed.
Lemma lem5319377 (l : real) (s : real -> Prop) (h1 : term334 l s) : (term22 s) = (has_sup s l).
Proof. exact (prop_ext (fun h2 : term22 s => @lem5319376 l s h2 h1) (fun h2 : has_sup s l => @lem5319362 l s h1)). Qed.
Lemma lem5319378 (l : real) (s : real -> Prop) (h1 : term334 l s) : has_sup s l.
Proof. exact (EQ_MP (@lem5319377 l s h1) (@lem5319362 l s h1)). Qed.
Lemma lem5319379 (s : real -> Prop) (l : real) : term737 s l.
Proof. exact (fun h0 : term334 l s => @lem5319378 l s h0). Qed.
Lemma lem5319380 (s : real -> Prop) (l : real) : term738 s l.
Proof. exact (conj (@lem5317174 l s) (@lem5319379 s l)). Qed.
Lemma lem5319381 (l : real) (s : real -> Prop) : (term738 s l) = ((has_sup s l) = (term334 l s)).
Proof. exact (@lem32 (has_sup s l) (term334 l s)). Qed.
Lemma lem5319382 (l : real) (s : real -> Prop) : (has_sup s l) = (term334 l s).
Proof. exact (EQ_MP (@lem5319381 l s) (@lem5319380 s l)). Qed.
Lemma lem5319387 (s : real -> Prop) : term739 s.
Proof. exact (fun l : real => @lem5319382 l s). Qed.
Lemma lem5319392 : term740.
Proof. exact (fun s : real -> Prop => @lem5319387 s). Qed.
