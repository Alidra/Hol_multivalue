Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1981473_term_abbrevs.
Require Import RAT_LEMMA2_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_LT_MUL_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm1979880_spec.
Require Import thm7_spec.
Lemma lem1981242 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1981243 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1981242 h1 x). Qed.
Lemma lem1981244 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1981245 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1981244 x) (@lem1981243 x h1)). Qed.
Lemma lem1981246 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1981245 x h1 y). Qed.
Lemma lem1981247 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1981248 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1981247 x y) (@lem1981246 x y h1)). Qed.
Lemma lem1981249 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1981250 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1981248 x y h1 (@lem1981249 x y h2)). Qed.
Lemma lem1981251 (x : real) (y : real) (h1 : term5 x y) : term7 x y.
Proof. exact (fun h0 : term0 => @lem1981250 x y h0 h1). Qed.
Lemma lem1981252 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1981253 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1981251 x y h2 (@lem1981252 h1)). Qed.
Lemma lem1981254 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : term5 x y => @lem1981253 x y h1 h0). Qed.
Lemma lem1981255 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1981254 x y h1). Qed.
Lemma lem1981256 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1981255 x h1). Qed.
Lemma lem1981257 : term8.
Proof. exact (fun h0 : term0 => @lem1981256 h0). Qed.
Lemma lem1981258 : term0.
Proof. exact (@lem1981257 (@lem1487565)). Qed.
Lemma lem1981259 (x : real) : term1 x.
Proof. exact (@lem1981258 x). Qed.
Lemma lem1981260 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1981261 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1981260 x) (@lem1981259 x)). Qed.
Lemma lem1981262 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1981261 x y). Qed.
Lemma lem1981263 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1981267 (x : real) (y : real) (h1 : (real_div x y) = (term9 x y)) : (real_div x y) = (term9 x y).
Proof. exact (h1). Qed.
Lemma lem1981268 (x : real) (y : real) (h1 : (real_div x y) = (term9 x y)) : (term9 x y) = (real_div x y).
Proof. exact (SYM (@lem1981267 x y h1)). Qed.
Lemma lem1981269 (x : real) (y : real) (h1 : (term9 x y) = (real_div x y)) : (term9 x y) = (real_div x y).
Proof. exact (h1). Qed.
Lemma lem1981270 (x : real) (y : real) (h1 : (term9 x y) = (real_div x y)) : (real_div x y) = (term9 x y).
Proof. exact (SYM (@lem1981269 x y h1)). Qed.
Lemma lem1981271 (x : real) (y : real) : ((real_div x y) = (term9 x y)) = ((term9 x y) = (real_div x y)).
Proof. exact (prop_ext (fun h1 : (real_div x y) = (term9 x y) => @lem1981268 x y h1) (fun h1 : (term9 x y) = (real_div x y) => @lem1981270 x y h1)). Qed.
Lemma lem1981272 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1981271 x y)). Qed.
Lemma lem1981273 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1981274 (x : real) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem1981273) (@lem1981272 x)). Qed.
Lemma lem1981275 : term14 = term15.
Proof. exact (fun_ext (fun x : real => @lem1981274 x)). Qed.
Lemma lem1981276 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1981277 : term16 = term17.
Proof. exact (MK_COMB (@lem1981276) (@lem1981275)). Qed.
Lemma lem1981278 : term17.
Proof. exact (EQ_MP (@lem1981277) (@lem1344936)). Qed.
Lemma lem1981281 (x : real) (y : real) (h1 : (term18 x y) = (term19 x y)) : (term18 x y) = (term19 x y).
Proof. exact (h1). Qed.
Lemma lem1981282 (x : real) (y : real) (h1 : (term18 x y) = (term19 x y)) : (term19 x y) = (term18 x y).
Proof. exact (SYM (@lem1981281 x y h1)). Qed.
Lemma lem1981283 (x : real) (y : real) (h1 : (term19 x y) = (term18 x y)) : (term19 x y) = (term18 x y).
Proof. exact (h1). Qed.
Lemma lem1981284 (x : real) (y : real) (h1 : (term19 x y) = (term18 x y)) : (term18 x y) = (term19 x y).
Proof. exact (SYM (@lem1981283 x y h1)). Qed.
Lemma lem1981285 (x : real) (y : real) : ((term18 x y) = (term19 x y)) = ((term19 x y) = (term18 x y)).
Proof. exact (prop_ext (fun h1 : (term18 x y) = (term19 x y) => @lem1981282 x y h1) (fun h1 : (term19 x y) = (term18 x y) => @lem1981284 x y h1)). Qed.
Lemma lem1981286 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1981285 x y)). Qed.
Lemma lem1981287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1981288 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1981287) (@lem1981286 x)). Qed.
Lemma lem1981289 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem1981288 x)). Qed.
Lemma lem1981290 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1981291 : term26 = term27.
Proof. exact (MK_COMB (@lem1981290) (@lem1981289)). Qed.
Lemma lem1981292 : term27.
Proof. exact (EQ_MP (@lem1981291) (@lem1595294)). Qed.
Lemma lem1981293 (x : real) : term28 x.
Proof. exact (@lem1981278 x). Qed.
Lemma lem1981294 (x : real) : (term28 x) = (term13 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1981295 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem1981294 x) (@lem1981293 x)). Qed.
Lemma lem1981296 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1981295 x y). Qed.
Lemma lem1981297 (x : real) (y : real) : (term29 x y) = ((term9 x y) = (real_div x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1981299 (x : real) : term30 x.
Proof. exact (@lem1981292 x). Qed.
Lemma lem1981300 (x : real) : (term30 x) = (term23 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1981301 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem1981300 x) (@lem1981299 x)). Qed.
Lemma lem1981302 (x : real) (y : real) : term31 x y.
Proof. exact (@lem1981301 x y). Qed.
Lemma lem1981303 (x : real) (y : real) : (term31 x y) = ((term19 x y) = (term18 x y)).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1981305 (y1 : real) (h1 : term32 y1) : term32 y1.
Proof. exact (h1). Qed.
Lemma lem1981306 (y2 : real) (h1 : term32 y2) : term32 y2.
Proof. exact (h1). Qed.
Lemma lem1981307 (y3 : real) (h1 : term32 y3) : term32 y3.
Proof. exact (h1). Qed.
Lemma lem1981309 (y1 : real) : (term32 y1) = ((term32 y1) = True).
Proof. exact (@lem7 (term32 y1)). Qed.
Lemma lem1981311 (y2 : real) : (term32 y2) = ((term32 y2) = True).
Proof. exact (@lem7 (term32 y2)). Qed.
Lemma lem1981322 (y1 : real) (h1 : term32 y1) : (term32 y1) = True.
Proof. exact (EQ_MP (@lem1981309 y1) (@lem1981305 y1 h1)). Qed.
Lemma lem1981323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1981324 (y1 : real) (h1 : term32 y1) : (term33 y1) = (and True).
Proof. exact (MK_COMB (@lem1981323) (@lem1981322 y1 h1)). Qed.
Lemma lem1981326 (y2 : real) (h1 : term32 y2) : (term32 y2) = True.
Proof. exact (EQ_MP (@lem1981311 y2) (@lem1981306 y2 h1)). Qed.
Lemma lem1981327 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term5 y1 y2) = (True /\ True).
Proof. exact (MK_COMB (@lem1981324 y1 h1) (@lem1981326 y2 h2)). Qed.
Lemma lem1981329 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981330 : (True /\ True) = True.
Proof. exact (@lem1981329 True). Qed.
Lemma lem1981331 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term5 y1 y2) = True.
Proof. exact (TRANS (@lem1981327 y1 y2 h1 h2) (@lem1981330)). Qed.
Lemma lem1981332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1981333 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term34 y1 y2) = (imp True).
Proof. exact (MK_COMB (@lem1981332) (@lem1981331 y1 y2 h1 h2)). Qed.
Lemma lem1981336 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)) = ((term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)).
Proof. exact (eq_refl ((term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2))). Qed.
Lemma lem1981337 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term37 x1 x2 y1 y2) = (term38 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981333 y1 y2 h1 h2) (@lem1981336 x1 x2 y1 y2)). Qed.
Lemma lem1981339 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1981340 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term38 x1 x2 y1 y2) = ((term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)).
Proof. exact (@lem1981339 ((term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2))). Qed.
Lemma lem1981343 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term37 x1 x2 y1 y2) = ((term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)).
Proof. exact (TRANS (@lem1981337 x1 x2 y1 y2 h1 h2) (@lem1981340 x1 x2 y1 y2)). Qed.
Lemma lem1981344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1981345 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term39 x1 x2 y1 y2) = (term40 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981344) (@lem1981343 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1981348 (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x3 : real) (y3 : real) : ((term35 x1 y1 x2 y2) = (real_div x3 y3)) = ((term35 x1 y1 x2 y2) = (real_div x3 y3)).
Proof. exact (eq_refl ((term35 x1 y1 x2 y2) = (real_div x3 y3))). Qed.
Lemma lem1981349 (x1 : real) (x2 : real) (x3 : real) (y3 : real) (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term41 x1 y1 x2 y2 x3 y3) = (term42 x1 y1 x2 y2 x3 y3).
Proof. exact (MK_COMB (@lem1981345 x1 x2 y1 y2 h1 h2) (@lem1981348 x1 y1 x2 y2 x3 y3)). Qed.
Lemma lem1981354 (x1 : real) (x2 : real) (x3 : real) (y3 : real) (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term42 x1 y1 x2 y2 x3 y3) = (term41 x1 y1 x2 y2 x3 y3).
Proof. exact (SYM (@lem1981349 x1 x2 x3 y3 y1 y2 h1 h2)). Qed.
Lemma lem1981355 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)) : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2).
Proof. exact (h1). Qed.
Lemma lem1981356 (x3 : real) (y3 : real) : (term43 x3 y3) = (term43 x3 y3).
Proof. exact (eq_refl (term43 x3 y3)). Qed.
Lemma lem1981357 (x3 : real) (y3 : real) (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)) : (term44 x3 y3 x1 y1 x2 y2) = (term45 x3 y3 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981356 x3 y3) (@lem1981355 x1 x2 y1 y2 h1)). Qed.
Lemma lem1981358 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : (term45 x3 y3 x1 x2 y1 y2) = ((term36 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (eq_refl (term45 x3 y3 x1 x2 y1 y2)). Qed.
Lemma lem1981359 (x3 : real) (y3 : real) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term46 x3 y3 x1 y1 x2 y2) = (term46 x3 y3 x1 y1 x2 y2).
Proof. exact (eq_refl (term46 x3 y3 x1 y1 x2 y2)). Qed.
Lemma lem1981360 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : ((term44 x3 y3 x1 y1 x2 y2) = (term45 x3 y3 x1 x2 y1 y2)) = ((term44 x3 y3 x1 y1 x2 y2) = ((term36 x1 x2 y1 y2) = (real_div x3 y3))).
Proof. exact (MK_COMB (@lem1981359 x3 y3 x1 y1 x2 y2) (@lem1981358 x1 x2 y1 y2 x3 y3)). Qed.
Lemma lem1981361 (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x3 : real) (y3 : real) : (term44 x3 y3 x1 y1 x2 y2) = ((term35 x1 y1 x2 y2) = (real_div x3 y3)).
Proof. exact (eq_refl (term44 x3 y3 x1 y1 x2 y2)). Qed.
Lemma lem1981362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1981363 (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x3 : real) (y3 : real) : (term46 x3 y3 x1 y1 x2 y2) = (term47 x1 y1 x2 y2 x3 y3).
Proof. exact (MK_COMB (@lem1981362) (@lem1981361 x1 y1 x2 y2 x3 y3)). Qed.
Lemma lem1981364 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : ((term36 x1 x2 y1 y2) = (real_div x3 y3)) = ((term36 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (eq_refl ((term36 x1 x2 y1 y2) = (real_div x3 y3))). Qed.
Lemma lem1981365 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : ((term44 x3 y3 x1 y1 x2 y2) = ((term36 x1 x2 y1 y2) = (real_div x3 y3))) = (((term35 x1 y1 x2 y2) = (real_div x3 y3)) = ((term36 x1 x2 y1 y2) = (real_div x3 y3))).
Proof. exact (MK_COMB (@lem1981363 x1 y1 x2 y2 x3 y3) (@lem1981364 x1 x2 y1 y2 x3 y3)). Qed.
Lemma lem1981366 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : ((term44 x3 y3 x1 y1 x2 y2) = (term45 x3 y3 x1 x2 y1 y2)) = (((term35 x1 y1 x2 y2) = (real_div x3 y3)) = ((term36 x1 x2 y1 y2) = (real_div x3 y3))).
Proof. exact (TRANS (@lem1981360 x1 x2 y1 y2 x3 y3) (@lem1981365 x1 x2 y1 y2 x3 y3)). Qed.
Lemma lem1981367 (x3 : real) (y3 : real) (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)) : ((term35 x1 y1 x2 y2) = (real_div x3 y3)) = ((term36 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (EQ_MP (@lem1981366 x1 x2 y1 y2 x3 y3) (@lem1981357 x3 y3 x1 x2 y1 y2 h1)). Qed.
Lemma lem1981368 (x3 : real) (y3 : real) (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)) : ((term36 x1 x2 y1 y2) = (real_div x3 y3)) = ((term35 x1 y1 x2 y2) = (real_div x3 y3)).
Proof. exact (SYM (@lem1981367 x3 y3 x1 x2 y1 y2 h1)). Qed.
Lemma lem1981372 (x : real) (y : real) : (term19 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem1981303 x y) (@lem1981302 x y)). Qed.
Lemma lem1981373 (y1 : real) (y2 : real) : (term19 y1 y2) = (term18 y1 y2).
Proof. exact (@lem1981372 y1 y2). Qed.
Lemma lem1981374 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term48 x1 y2 x2 y1) = (term48 x1 y2 x2 y1).
Proof. exact (eq_refl (term48 x1 y2 x2 y1)). Qed.
Lemma lem1981375 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term36 x1 x2 y1 y2) = (term49 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981374 x1 y2 x2 y1) (@lem1981373 y1 y2)). Qed.
Lemma lem1981377 (x : real) (y : real) : (term9 x y) = (real_div x y).
Proof. exact (EQ_MP (@lem1981297 x y) (@lem1981296 x y)). Qed.
Lemma lem1981378 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term49 x1 x2 y1 y2) = (term50 x1 x2 y1 y2).
Proof. exact (@lem1981377 (term51 x1 y2 x2 y1) (real_mul y1 y2)). Qed.
Lemma lem1981379 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term36 x1 x2 y1 y2) = (term50 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1981375 x1 x2 y1 y2) (@lem1981378 x1 x2 y1 y2)). Qed.
Lemma lem1981380 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981381 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term52 x1 x2 y1 y2) = (term53 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981380) (@lem1981379 x1 x2 y1 y2)). Qed.
Lemma lem1981382 (x3 : real) (y3 : real) : (real_div x3 y3) = (real_div x3 y3).
Proof. exact (eq_refl (real_div x3 y3)). Qed.
Lemma lem1981383 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : ((term36 x1 x2 y1 y2) = (real_div x3 y3)) = ((term50 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (MK_COMB (@lem1981381 x1 x2 y1 y2) (@lem1981382 x3 y3)). Qed.
Lemma lem1981386 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (x3 : real) (y3 : real) : ((term50 x1 x2 y1 y2) = (real_div x3 y3)) = ((term36 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (SYM (@lem1981383 x1 x2 y1 y2 x3 y3)). Qed.
Lemma lem1981387 (y1 : real) (y2 : real) (y3 : real) (h1 : term54 y1 y2 y3) : term54 y1 y2 y3.
Proof. exact (h1). Qed.
Lemma lem1981392 (y3 : real) : (term32 y3) = ((term32 y3) = True).
Proof. exact (@lem7 (term32 y3)). Qed.
Lemma lem1981397 (y3 : real) (h1 : term32 y3) : (term32 y3) = True.
Proof. exact (EQ_MP (@lem1981392 y3) (@lem1981307 y3 h1)). Qed.
Lemma lem1981398 (y1 : real) (y2 : real) : (term55 y1 y2) = (term55 y1 y2).
Proof. exact (eq_refl (term55 y1 y2)). Qed.
Lemma lem1981399 (y1 : real) (y2 : real) (y3 : real) (h1 : term32 y3) : (term54 y1 y2 y3) = (term56 y1 y2).
Proof. exact (MK_COMB (@lem1981398 y1 y2) (@lem1981397 y3 h1)). Qed.
Lemma lem1981401 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1981402 (y1 : real) (y2 : real) : (term56 y1 y2) = (term6 y1 y2).
Proof. exact (@lem1981401 (term6 y1 y2)). Qed.
Lemma lem1981403 (y1 : real) (y2 : real) (y3 : real) (h1 : term32 y3) : (term54 y1 y2 y3) = (term6 y1 y2).
Proof. exact (TRANS (@lem1981399 y1 y2 y3 h1) (@lem1981402 y1 y2)). Qed.
Lemma lem1981404 (y1 : real) (y2 : real) (y3 : real) (h1 : term32 y3) : (term6 y1 y2) = (term54 y1 y2 y3).
Proof. exact (SYM (@lem1981403 y1 y2 y3 h1)). Qed.
Lemma lem1981406 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1981263 x y) (@lem1981262 x y)). Qed.
Lemma lem1981407 (y1 : real) (y2 : real) : term4 y1 y2.
Proof. exact (@lem1981406 y1 y2). Qed.
Lemma lem1981408 (y1 : real) : (term32 y1) = ((term32 y1) = True).
Proof. exact (@lem7 (term32 y1)). Qed.
Lemma lem1981410 (y2 : real) : (term32 y2) = ((term32 y2) = True).
Proof. exact (@lem7 (term32 y2)). Qed.
Lemma lem1981417 (y1 : real) (h1 : term32 y1) : (term32 y1) = True.
Proof. exact (EQ_MP (@lem1981408 y1) (@lem1981305 y1 h1)). Qed.
Lemma lem1981418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1981419 (y1 : real) (h1 : term32 y1) : (term33 y1) = (and True).
Proof. exact (MK_COMB (@lem1981418) (@lem1981417 y1 h1)). Qed.
Lemma lem1981421 (y2 : real) (h1 : term32 y2) : (term32 y2) = True.
Proof. exact (EQ_MP (@lem1981410 y2) (@lem1981306 y2 h1)). Qed.
Lemma lem1981422 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term5 y1 y2) = (True /\ True).
Proof. exact (MK_COMB (@lem1981419 y1 h1) (@lem1981421 y2 h2)). Qed.
Lemma lem1981424 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981425 : (True /\ True) = True.
Proof. exact (@lem1981424 True). Qed.
Lemma lem1981426 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : (term5 y1 y2) = True.
Proof. exact (TRANS (@lem1981422 y1 y2 h1 h2) (@lem1981425)). Qed.
Lemma lem1981427 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : True = (term5 y1 y2).
Proof. exact (SYM (@lem1981426 y1 y2 h1 h2)). Qed.
Lemma lem1981428 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : term5 y1 y2.
Proof. exact (EQ_MP (@lem1981427 y1 y2 h1 h2) (@lem0)). Qed.
Lemma lem1981429 (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : term6 y1 y2.
Proof. exact (@lem1981407 y1 y2 (@lem1981428 y1 y2 h1 h2)). Qed.
Lemma lem1981430 (y1 : real) (y2 : real) (y3 : real) (h1 : term32 y1) (h2 : term32 y2) (h3 : term32 y3) : term54 y1 y2 y3.
Proof. exact (EQ_MP (@lem1981404 y1 y2 y3 h3) (@lem1981429 y1 y2 h1 h2)). Qed.
Lemma lem1981431 (y1 : real) (y2 : real) (y3 : real) (h1 : term54 y1 y2 y3) : term54 y1 y2 y3.
Proof. exact (h1). Qed.
Lemma lem1981433 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term57 x1 y2 x2 y1.
Proof. exact (fun h0 : term5 y1 y2 => @lem1979880 x1 x2 y1 y2 h0). Qed.
Lemma lem1981434 (x1 : real) (y3 : real) (x2 : real) (y1 : real) (y2 : real) : term58 x1 y3 x2 y1 y2.
Proof. exact (@lem1981433 x1 y3 x2 (real_mul y1 y2)). Qed.
Lemma lem1981443 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : term54 y1 y2 y3) : ((term59 x1 y1 y2) = (real_div x2 y3)) = ((real_mul x1 y3) = (term60 x2 y1 y2)).
Proof. exact (@lem1981434 x1 y3 x2 y1 y2 (@lem1981431 y1 y2 y3 h1)). Qed.
Lemma lem1981444 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : term54 y1 y2 y3) : ((term50 x1 x2 y1 y2) = (real_div x3 y3)) = ((term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)).
Proof. exact (@lem1981443 (term51 x1 y2 x2 y1) x3 y1 y2 y3 h1). Qed.
Lemma lem1981448 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2).
Proof. exact (h1). Qed.
Lemma lem1981449 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981450 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : (term62 x1 y2 x2 y1 y3) = (term63 x3 y1 y2).
Proof. exact (MK_COMB (@lem1981449) (@lem1981448 x1 x2 y3 x3 y1 y2 h1)). Qed.
Lemma lem1981451 (x3 : real) (y1 : real) (y2 : real) : (term60 x3 y1 y2) = (term60 x3 y1 y2).
Proof. exact (eq_refl (term60 x3 y1 y2)). Qed.
Lemma lem1981452 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : ((term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) = ((term60 x3 y1 y2) = (term60 x3 y1 y2)).
Proof. exact (MK_COMB (@lem1981450 x1 x2 y3 x3 y1 y2 h1) (@lem1981451 x3 y1 y2)). Qed.
Lemma lem1981454 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1981455 (x : real) : (x = x) = True.
Proof. exact (@lem1981454 real x). Qed.
Lemma lem1981456 (x3 : real) (y1 : real) (y2 : real) : ((term60 x3 y1 y2) = (term60 x3 y1 y2)) = True.
Proof. exact (@lem1981455 (term60 x3 y1 y2)). Qed.
Lemma lem1981457 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : ((term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) = True.
Proof. exact (TRANS (@lem1981452 x1 x2 y3 x3 y1 y2 h1) (@lem1981456 x3 y1 y2)). Qed.
Lemma lem1981458 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : term54 y1 y2 y3) (h2 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : ((term50 x1 x2 y1 y2) = (real_div x3 y3)) = True.
Proof. exact (TRANS (@lem1981444 x1 x2 x3 y1 y2 y3 h1) (@lem1981457 x1 x2 y3 x3 y1 y2 h2)). Qed.
Lemma lem1981459 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : term54 y1 y2 y3) (h2 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : True = ((term50 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (SYM (@lem1981458 x1 x2 y3 x3 y1 y2 h1 h2)). Qed.
Lemma lem1981460 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : term54 y1 y2 y3) (h2 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : (term50 x1 x2 y1 y2) = (real_div x3 y3).
Proof. exact (EQ_MP (@lem1981459 x1 x2 y3 x3 y1 y2 h1 h2) (@lem0)). Qed.
Lemma lem1981461 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : term64 x1 x2 y1 y2 x3 y3.
Proof. exact (fun h0 : term54 y1 y2 y3 => @lem1981460 x1 x2 y3 x3 y1 y2 h0 h1). Qed.
Lemma lem1981462 (x1 : real) (x2 : real) (y3 : real) (x3 : real) (y1 : real) (y2 : real) (h1 : term54 y1 y2 y3) (h2 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) : (term50 x1 x2 y1 y2) = (real_div x3 y3).
Proof. exact (@lem1981461 x1 x2 y3 x3 y1 y2 h2 (@lem1981387 y1 y2 y3 h1)). Qed.
Lemma lem1981463 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h2 : term32 y1) (h3 : term32 y2) (h4 : term32 y3) : (term54 y1 y2 y3) = ((term50 x1 x2 y1 y2) = (real_div x3 y3)).
Proof. exact (prop_ext (fun h5 : term54 y1 y2 y3 => @lem1981462 x1 x2 y3 x3 y1 y2 h5 h1) (fun h5 : (term50 x1 x2 y1 y2) = (real_div x3 y3) => @lem1981430 y1 y2 y3 h2 h3 h4)). Qed.
Lemma lem1981464 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h2 : term32 y1) (h3 : term32 y2) (h4 : term32 y3) : (term50 x1 x2 y1 y2) = (real_div x3 y3).
Proof. exact (EQ_MP (@lem1981463 x1 x2 x3 y1 y2 y3 h1 h2 h3 h4) (@lem1981430 y1 y2 y3 h2 h3 h4)). Qed.
Lemma lem1981465 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h2 : term32 y1) (h3 : term32 y2) (h4 : term32 y3) : (term36 x1 x2 y1 y2) = (real_div x3 y3).
Proof. exact (EQ_MP (@lem1981386 x1 x2 y1 y2 x3 y3) (@lem1981464 x1 x2 x3 y1 y2 y3 h1 h2 h3 h4)). Qed.
Lemma lem1981466 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2)) (h2 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h3 : term32 y1) (h4 : term32 y2) (h5 : term32 y3) : (term35 x1 y1 x2 y2) = (real_div x3 y3).
Proof. exact (EQ_MP (@lem1981368 x3 y3 x1 x2 y1 y2 h1) (@lem1981465 x1 x2 x3 y1 y2 y3 h2 h3 h4 h5)). Qed.
Lemma lem1981467 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h2 : term32 y1) (h3 : term32 y2) (h4 : term32 y3) : term42 x1 y1 x2 y2 x3 y3.
Proof. exact (fun h0 : (term35 x1 y1 x2 y2) = (term36 x1 x2 y1 y2) => @lem1981466 x1 x2 x3 y1 y2 y3 h0 h1 h2 h3 h4). Qed.
Lemma lem1981468 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h2 : term32 y1) (h3 : term32 y2) (h4 : term32 y3) : term41 x1 y1 x2 y2 x3 y3.
Proof. exact (EQ_MP (@lem1981354 x1 x2 x3 y3 y1 y2 h2 h3) (@lem1981467 x1 x2 x3 y1 y2 y3 h1 h2 h3 h4)). Qed.
Lemma lem1981469 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2)) (h2 : term32 y1) (h3 : term32 y2) (h4 : term32 y3) : (term35 x1 y1 x2 y2) = (real_div x3 y3).
Proof. exact (@lem1981468 x1 x2 x3 y1 y2 y3 h1 h2 h3 h4 (@lem1978261 x1 x2 y1 y2)). Qed.
Lemma lem1981470 (x1 : real) (x2 : real) (x3 : real) (y1 : real) (y2 : real) (y3 : real) (h1 : term32 y1) (h2 : term32 y2) (h3 : term32 y3) : term65 x1 y1 x2 y2 x3 y3.
Proof. exact (fun h0 : (term61 x1 y2 x2 y1 y3) = (term60 x3 y1 y2) => @lem1981469 x1 x2 x3 y1 y2 y3 h0 h1 h2 h3). Qed.
Lemma lem1981471 (x1 : real) (x2 : real) (x3 : real) (y3 : real) (y1 : real) (y2 : real) (h1 : term32 y1) (h2 : term32 y2) : term66 x1 y1 x2 y2 x3 y3.
Proof. exact (fun h0 : term32 y3 => @lem1981470 x1 x2 x3 y1 y2 y3 h1 h2 h0). Qed.
Lemma lem1981472 (x1 : real) (x2 : real) (y2 : real) (x3 : real) (y3 : real) (y1 : real) (h1 : term32 y1) : term67 x1 y1 x2 y2 x3 y3.
Proof. exact (fun h0 : term32 y2 => @lem1981471 x1 x2 x3 y3 y1 y2 h1 h0). Qed.
Lemma lem1981473 (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x3 : real) (y3 : real) : term68 x1 y1 x2 y2 x3 y3.
Proof. exact (fun h0 : term32 y1 => @lem1981472 x1 x2 y2 x3 y3 y1 h0). Qed.
