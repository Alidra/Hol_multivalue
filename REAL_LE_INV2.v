Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INV2_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_LE_LT_spec.
Require Import REAL_LT_INV2_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1632195 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1632196 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1632195 h1 x). Qed.
Lemma lem1632197 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1632198 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1632197 x) (@lem1632196 x h1)). Qed.
Lemma lem1632199 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1632198 x h1 y). Qed.
Lemma lem1632200 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1632201 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1632200 y x) (@lem1632199 x y h1)). Qed.
Lemma lem1632202 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1632203 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1632201 y x h1 (@lem1632202 x y h2)). Qed.
Lemma lem1632204 (x : real) (y : real) (h1 : term5 x y) : term7 y x.
Proof. exact (fun h0 : term0 => @lem1632203 x y h0 h1). Qed.
Lemma lem1632205 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1632206 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1632204 x y h2 (@lem1632205 h1)). Qed.
Lemma lem1632207 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun h0 : term5 x y => @lem1632206 x y h1 h0). Qed.
Lemma lem1632208 (y : real) (h1 : term0) : term8 y.
Proof. exact (fun x : real => @lem1632207 y x h1). Qed.
Lemma lem1632209 (h1 : term0) : term9.
Proof. exact (fun y : real => @lem1632208 y h1). Qed.
Lemma lem1632210 : term10.
Proof. exact (fun h0 : term0 => @lem1632209 h0). Qed.
Lemma lem1632211 : term9.
Proof. exact (@lem1632210 (@lem1632194)). Qed.
Lemma lem1632212 (y : real) : term11 y.
Proof. exact (@lem1632211 y). Qed.
Lemma lem1632213 (y : real) : (term11 y) = (term8 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1632214 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1632213 y) (@lem1632212 y)). Qed.
Lemma lem1632215 (y : real) (x : real) : term12 y x.
Proof. exact (@lem1632214 y x). Qed.
Lemma lem1632216 (y : real) (x : real) : (term12 y x) = (term4 y x).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1632218 (x : real) (y : real) : term13 x y.
Proof. exact (@lem9784 (x = y)). Qed.
Lemma lem1632219 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1632220 (x : real) (y : real) : term14 x y.
Proof. exact (EQ_MP (@lem1632219 x y) (@lem1632218 x y)). Qed.
Lemma lem1632222 (x : real) (y : real) (h1 : term15 x y) : term15 x y.
Proof. exact (h1). Qed.
Lemma lem1632223 (x : real) : term16 x.
Proof. exact (@lem1376325 x). Qed.
Lemma lem1632224 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1632225 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1632224 x) (@lem1632223 x)). Qed.
Lemma lem1632226 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1632225 x y). Qed.
Lemma lem1632227 (x : real) (y : real) : (term18 x y) = ((real_le x y) = (term19 x y)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1632234 (x : real) (y : real) : (real_le x y) = (term19 x y).
Proof. exact (EQ_MP (@lem1632227 x y) (@lem1632226 x y)). Qed.
Lemma lem1632239 (x : real) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1632240 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1632239 x) (@lem1632234 x y)). Qed.
Lemma lem1632243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632244 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1632243) (@lem1632240 x y)). Qed.
Lemma lem1632246 (x : real) (y : real) : (real_le x y) = (term19 x y).
Proof. exact (EQ_MP (@lem1632227 x y) (@lem1632226 x y)). Qed.
Lemma lem1632247 (y : real) (x : real) : (term25 y x) = (term26 y x).
Proof. exact (@lem1632246 (real_inv y) (real_inv x)). Qed.
Lemma lem1632252 (y : real) (x : real) : (term27 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1632244 x y) (@lem1632247 y x)). Qed.
Lemma lem1632255 (y : real) (x : real) : (term28 y x) = (term27 y x).
Proof. exact (SYM (@lem1632252 y x)). Qed.
Lemma lem1632261 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1632262 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1632263 (x : real) (y : real) (h1 : x = y) : (term30 x) = (term30 y).
Proof. exact (MK_COMB (@lem1632262) (@lem1632261 x y h1)). Qed.
Lemma lem1632264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632265 (x : real) (y : real) (h1 : x = y) : (term20 x) = (term20 y).
Proof. exact (MK_COMB (@lem1632264) (@lem1632263 x y h1)). Qed.
Lemma lem1632269 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1632270 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1632271 (x : real) (y : real) (h1 : x = y) : (real_lt x) = (real_lt y).
Proof. exact (MK_COMB (@lem1632270) (@lem1632269 x y h1)). Qed.
Lemma lem1632272 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1632273 (x : real) (y : real) (h1 : x = y) : (real_lt x y) = (real_lt y y).
Proof. exact (MK_COMB (@lem1632271 x y h1) (@lem1632272 y)). Qed.
Lemma lem1632274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1632275 (x : real) (y : real) (h1 : x = y) : (term31 x y) = (term32 y).
Proof. exact (MK_COMB (@lem1632274) (@lem1632273 x y h1)). Qed.
Lemma lem1632279 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1632280 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1632281 (x : real) (y : real) (h1 : x = y) : (@eq real x) = (@eq real y).
Proof. exact (MK_COMB (@lem1632280) (@lem1632279 x y h1)). Qed.
Lemma lem1632282 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1632283 (x : real) (y : real) (h1 : x = y) : (x = y) = (y = y).
Proof. exact (MK_COMB (@lem1632281 x y h1) (@lem1632282 y)). Qed.
Lemma lem1632285 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1632286 (x : real) : (x = x) = True.
Proof. exact (@lem1632285 real x). Qed.
Lemma lem1632287 (y : real) : (y = y) = True.
Proof. exact (@lem1632286 y). Qed.
Lemma lem1632288 (x : real) (y : real) (h1 : x = y) : (x = y) = True.
Proof. exact (TRANS (@lem1632283 x y h1) (@lem1632287 y)). Qed.
Lemma lem1632289 (x : real) (y : real) (h1 : x = y) : (term19 x y) = (term33 y).
Proof. exact (MK_COMB (@lem1632275 x y h1) (@lem1632288 x y h1)). Qed.
Lemma lem1632291 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1632292 (y : real) : (term33 y) = True.
Proof. exact (@lem1632291 (real_lt y y)). Qed.
Lemma lem1632293 (x : real) (y : real) (h1 : x = y) : (term19 x y) = True.
Proof. exact (TRANS (@lem1632289 x y h1) (@lem1632292 y)). Qed.
Lemma lem1632294 (x : real) (y : real) (h1 : x = y) : (term22 x y) = (term34 y).
Proof. exact (MK_COMB (@lem1632265 x y h1) (@lem1632293 x y h1)). Qed.
Lemma lem1632296 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1632297 (y : real) : (term34 y) = (term30 y).
Proof. exact (@lem1632296 (term30 y)). Qed.
Lemma lem1632298 (x : real) (y : real) (h1 : x = y) : (term22 x y) = (term30 y).
Proof. exact (TRANS (@lem1632294 x y h1) (@lem1632297 y)). Qed.
Lemma lem1632299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632300 (x : real) (y : real) (h1 : x = y) : (term24 x y) = (term35 y).
Proof. exact (MK_COMB (@lem1632299) (@lem1632298 x y h1)). Qed.
Lemma lem1632304 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1632305 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1632306 (x : real) (y : real) (h1 : x = y) : (real_inv x) = (real_inv y).
Proof. exact (MK_COMB (@lem1632305) (@lem1632304 x y h1)). Qed.
Lemma lem1632307 (y : real) : (term36 y) = (term36 y).
Proof. exact (eq_refl (term36 y)). Qed.
Lemma lem1632308 (x : real) (y : real) (h1 : x = y) : (term6 y x) = (term37 y).
Proof. exact (MK_COMB (@lem1632307 y) (@lem1632306 x y h1)). Qed.
Lemma lem1632309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1632310 (x : real) (y : real) (h1 : x = y) : (term38 y x) = (term39 y).
Proof. exact (MK_COMB (@lem1632309) (@lem1632308 x y h1)). Qed.
Lemma lem1632314 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1632315 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1632316 (x : real) (y : real) (h1 : x = y) : (real_inv x) = (real_inv y).
Proof. exact (MK_COMB (@lem1632315) (@lem1632314 x y h1)). Qed.
Lemma lem1632317 (y : real) : (term40 y) = (term40 y).
Proof. exact (eq_refl (term40 y)). Qed.
Lemma lem1632318 (x : real) (y : real) (h1 : x = y) : ((real_inv y) = (real_inv x)) = ((real_inv y) = (real_inv y)).
Proof. exact (MK_COMB (@lem1632317 y) (@lem1632316 x y h1)). Qed.
Lemma lem1632320 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1632321 (x : real) : (x = x) = True.
Proof. exact (@lem1632320 real x). Qed.
Lemma lem1632322 (y : real) : ((real_inv y) = (real_inv y)) = True.
Proof. exact (@lem1632321 (real_inv y)). Qed.
Lemma lem1632323 (x : real) (y : real) (h1 : x = y) : ((real_inv y) = (real_inv x)) = True.
Proof. exact (TRANS (@lem1632318 x y h1) (@lem1632322 y)). Qed.
Lemma lem1632324 (x : real) (y : real) (h1 : x = y) : (term26 y x) = (term41 y).
Proof. exact (MK_COMB (@lem1632310 x y h1) (@lem1632323 x y h1)). Qed.
Lemma lem1632326 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1632327 (y : real) : (term41 y) = True.
Proof. exact (@lem1632326 (term37 y)). Qed.
Lemma lem1632328 (x : real) (y : real) (h1 : x = y) : (term26 y x) = True.
Proof. exact (TRANS (@lem1632324 x y h1) (@lem1632327 y)). Qed.
Lemma lem1632329 (x : real) (y : real) (h1 : x = y) : (term28 y x) = (term42 y).
Proof. exact (MK_COMB (@lem1632300 x y h1) (@lem1632328 x y h1)). Qed.
Lemma lem1632331 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1632332 (y : real) : (term42 y) = True.
Proof. exact (@lem1632331 (term30 y)). Qed.
Lemma lem1632333 (x : real) (y : real) (h1 : x = y) : (term28 y x) = True.
Proof. exact (TRANS (@lem1632329 x y h1) (@lem1632332 y)). Qed.
Lemma lem1632334 (x : real) (y : real) (h1 : x = y) : True = (term28 y x).
Proof. exact (SYM (@lem1632333 x y h1)). Qed.
Lemma lem1632335 (x : real) (y : real) (h1 : x = y) : term28 y x.
Proof. exact (EQ_MP (@lem1632334 x y h1) (@lem0)). Qed.
Lemma lem1632336 (x : real) (y : real) : term43 x y.
Proof. exact (@lem82 (x = y)). Qed.
Lemma lem1632356 (x : real) (y : real) (h1 : term15 x y) : (x = y) = False.
Proof. exact (@lem1632336 x y (@lem1632222 x y h1)). Qed.
Lemma lem1632357 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1632358 (x : real) (y : real) (h1 : term15 x y) : (term19 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1632357 x y) (@lem1632356 x y h1)). Qed.
Lemma lem1632360 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1632361 (x : real) (y : real) : (term44 x y) = (real_lt x y).
Proof. exact (@lem1632360 (real_lt x y)). Qed.
Lemma lem1632362 (x : real) (y : real) (h1 : term15 x y) : (term19 x y) = (real_lt x y).
Proof. exact (TRANS (@lem1632358 x y h1) (@lem1632361 x y)). Qed.
Lemma lem1632363 (x : real) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1632364 (x : real) (y : real) (h1 : term15 x y) : (term22 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1632363 x) (@lem1632362 x y h1)). Qed.
Lemma lem1632367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632368 (x : real) (y : real) (h1 : term15 x y) : (term24 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1632367) (@lem1632364 x y h1)). Qed.
Lemma lem1632373 (y : real) (x : real) : (term26 y x) = (term26 y x).
Proof. exact (eq_refl (term26 y x)). Qed.
Lemma lem1632374 (x : real) (y : real) (h1 : term15 x y) : (term28 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem1632368 x y h1) (@lem1632373 y x)). Qed.
Lemma lem1632377 (x : real) (y : real) (h1 : term15 x y) : (term46 y x) = (term28 y x).
Proof. exact (SYM (@lem1632374 x y h1)). Qed.
Lemma lem1632378 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1632379 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1632380 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1632382 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1632216 y x) (@lem1632215 y x)). Qed.
Lemma lem1632396 (x : real) : (term30 x) = ((term30 x) = True).
Proof. exact (@lem7 (term30 x)). Qed.
Lemma lem1632398 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1632403 (x : real) (h1 : term30 x) : (term30 x) = True.
Proof. exact (EQ_MP (@lem1632396 x) (@lem1632380 x h1)). Qed.
Lemma lem1632404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632405 (x : real) (h1 : term30 x) : (term20 x) = (and True).
Proof. exact (MK_COMB (@lem1632404) (@lem1632403 x h1)). Qed.
Lemma lem1632407 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1632398 x y) (@lem1632379 x y h1)). Qed.
Lemma lem1632408 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : (term5 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1632405 x h2) (@lem1632407 x y h1)). Qed.
Lemma lem1632410 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1632411 : (True /\ True) = True.
Proof. exact (@lem1632410 True). Qed.
Lemma lem1632412 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : (term5 x y) = True.
Proof. exact (TRANS (@lem1632408 y x h1 h2) (@lem1632411)). Qed.
Lemma lem1632413 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : True = (term5 x y).
Proof. exact (SYM (@lem1632412 y x h1 h2)). Qed.
Lemma lem1632414 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : term5 x y.
Proof. exact (EQ_MP (@lem1632413 y x h1 h2) (@lem0)). Qed.
Lemma lem1632415 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : term6 y x.
Proof. exact (@lem1632382 y x (@lem1632414 y x h1 h2)). Qed.
Lemma lem1632416 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : term26 y x.
Proof. exact (or_intro1 (@lem1632415 y x h1 h2) ((real_inv y) = (real_inv x))). Qed.
Lemma lem1632417 (x : real) (y : real) (h1 : term5 x y) : real_lt x y.
Proof. exact (proj2 (@lem1632378 x y h1)). Qed.
Lemma lem1632418 (x : real) (y : real) (h1 : term5 x y) : term30 x.
Proof. exact (proj1 (@lem1632378 x y h1)). Qed.
Lemma lem1632419 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : (real_lt x y) = (term26 y x).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1632416 y x h1 h2) (fun h3 : term26 y x => @lem1632379 x y h1)). Qed.
Lemma lem1632420 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : term26 y x.
Proof. exact (EQ_MP (@lem1632419 y x h1 h2) (@lem1632379 x y h1)). Qed.
Lemma lem1632421 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : (term30 x) = (term26 y x).
Proof. exact (prop_ext (fun h3 : term30 x => @lem1632420 y x h1 h2) (fun h3 : term26 y x => @lem1632380 x h2)). Qed.
Lemma lem1632422 (y : real) (x : real) (h1 : real_lt x y) (h2 : term30 x) : term26 y x.
Proof. exact (EQ_MP (@lem1632421 y x h1 h2) (@lem1632380 x h2)). Qed.
Lemma lem1632423 (y : real) (x : real) (h1 : term5 x y) (h2 : term30 x) : (real_lt x y) = (term26 y x).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1632422 y x h3 h2) (fun h3 : term26 y x => @lem1632417 x y h1)). Qed.
Lemma lem1632424 (y : real) (x : real) (h1 : term5 x y) (h2 : term30 x) : term26 y x.
Proof. exact (EQ_MP (@lem1632423 y x h1 h2) (@lem1632417 x y h1)). Qed.
Lemma lem1632425 (x : real) (y : real) (h1 : term5 x y) : (term30 x) = (term26 y x).
Proof. exact (prop_ext (fun h2 : term30 x => @lem1632424 y x h1 h2) (fun h2 : term26 y x => @lem1632418 x y h1)). Qed.
Lemma lem1632426 (x : real) (y : real) (h1 : term5 x y) : term26 y x.
Proof. exact (EQ_MP (@lem1632425 x y h1) (@lem1632418 x y h1)). Qed.
Lemma lem1632427 (y : real) (x : real) : term46 y x.
Proof. exact (fun h0 : term5 x y => @lem1632426 x y h0). Qed.
Lemma lem1632428 (x : real) (y : real) (h1 : term15 x y) : term28 y x.
Proof. exact (EQ_MP (@lem1632377 x y h1) (@lem1632427 y x)). Qed.
Lemma lem1632429 (y : real) (x : real) : term28 y x.
Proof. exact (or_elim (@lem1632220 x y) (fun h0 : x = y => @lem1632335 x y h0) (fun h0 : term15 x y => @lem1632428 x y h0)). Qed.
Lemma lem1632430 (y : real) (x : real) : term27 y x.
Proof. exact (EQ_MP (@lem1632255 y x) (@lem1632429 y x)). Qed.
Lemma lem1632435 (x : real) : term47 x.
Proof. exact (fun y : real => @lem1632430 y x). Qed.
Lemma lem1632440 : term48.
Proof. exact (fun x : real => @lem1632435 x). Qed.
