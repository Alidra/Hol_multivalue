Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_mul_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1324272 : treal_mul = term0.
Proof. exact (@treal_mul_def). Qed.
Lemma lem1324273 (_23630 : prod hreal hreal) : _23630 = _23630.
Proof. exact (eq_refl _23630). Qed.
Lemma lem1324274 (_23630 : prod hreal hreal) : (treal_mul _23630) = (term1 _23630).
Proof. exact (MK_COMB (@lem1324272) (@lem1324273 _23630)). Qed.
Lemma lem1324275 (_23630 : prod hreal hreal) : (term1 _23630) = (term2 _23630).
Proof. exact (eq_refl (term1 _23630)). Qed.
Lemma lem1324276 (_23630 : prod hreal hreal) : (treal_mul _23630) = (term2 _23630).
Proof. exact (TRANS (@lem1324274 _23630) (@lem1324275 _23630)). Qed.
Lemma lem1324277 (_23631 : prod hreal hreal) : _23631 = _23631.
Proof. exact (eq_refl _23631). Qed.
Lemma lem1324278 (_23630 : prod hreal hreal) (_23631 : prod hreal hreal) : (treal_mul _23630 _23631) = (term3 _23630 _23631).
Proof. exact (MK_COMB (@lem1324276 _23630) (@lem1324277 _23631)). Qed.
Lemma lem1324279 (_23630 : prod hreal hreal) (_23631 : prod hreal hreal) : (term3 _23630 _23631) = (term4 _23630 _23631).
Proof. exact (eq_refl (term3 _23630 _23631)). Qed.
Lemma lem1324280 (_23630 : prod hreal hreal) (_23631 : prod hreal hreal) : (treal_mul _23630 _23631) = (term4 _23630 _23631).
Proof. exact (TRANS (@lem1324278 _23630 _23631) (@lem1324279 _23630 _23631)). Qed.
Lemma lem1324281 (_23630 : prod hreal hreal) : term5 _23630.
Proof. exact (fun _23631 : prod hreal hreal => @lem1324280 _23630 _23631). Qed.
Lemma lem1324282 : term6.
Proof. exact (fun _23630 : prod hreal hreal => @lem1324281 _23630). Qed.
Lemma lem1324283 (_23630 : prod hreal hreal) : term7 _23630.
Proof. exact (@lem1324282 _23630). Qed.
Lemma lem1324284 (_23630 : prod hreal hreal) : (term7 _23630) = (term5 _23630).
Proof. exact (eq_refl (term7 _23630)). Qed.
Lemma lem1324285 (_23630 : prod hreal hreal) : term5 _23630.
Proof. exact (EQ_MP (@lem1324284 _23630) (@lem1324283 _23630)). Qed.
Lemma lem1324286 (_23630 : prod hreal hreal) (_23631 : prod hreal hreal) : term8 _23630 _23631.
Proof. exact (@lem1324285 _23630 _23631). Qed.
Lemma lem1324287 (_23630 : prod hreal hreal) (_23631 : prod hreal hreal) : (term8 _23630 _23631) = ((treal_mul _23630 _23631) = (term4 _23630 _23631)).
Proof. exact (eq_refl (term8 _23630 _23631)). Qed.
Lemma lem1324288 (_23630 : prod hreal hreal) (_23631 : prod hreal hreal) : (treal_mul _23630 _23631) = (term4 _23630 _23631).
Proof. exact (EQ_MP (@lem1324287 _23630 _23631) (@lem1324286 _23630 _23631)). Qed.
Lemma lem1324289 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term9 x1 y1 x2 y2) = (term10 x1 y1 x2 y2).
Proof. exact (@lem1324288 (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)). Qed.
Lemma lem1324290 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1324291 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1324292 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1324291 A B x) (@lem1324290 A B x)). Qed.
Lemma lem1324293 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1324292 A B x y). Qed.
Lemma lem1324294 {A B : Type'} (x : A) (y : B) : (term13 A B x y) = ((term14 A B x y) = y).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1324296 {A B : Type'} (x : A) : term15 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1324297 {A B : Type'} (x : A) : (term15 A B x) = (term16 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem1324298 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (EQ_MP (@lem1324297 A B x) (@lem1324296 A B x)). Qed.
Lemma lem1324299 {A B : Type'} (x : A) (y : B) : term17 A B x y.
Proof. exact (@lem1324298 A B x y). Qed.
Lemma lem1324300 {A B : Type'} (y : B) (x : A) : (term17 A B x y) = ((term18 A B x y) = x).
Proof. exact (eq_refl (term17 A B x y)). Qed.
Lemma lem1324303 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1324300 A B y x) (@lem1324299 A B x y)). Qed.
Lemma lem1324304 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1324303 hreal hreal y x). Qed.
Lemma lem1324305 (y1 : hreal) (x1 : hreal) : (term19 x1 y1) = x1.
Proof. exact (@lem1324304 y1 x1). Qed.
Lemma lem1324306 (x1 : hreal) (y1 : hreal) : x1 = (term19 x1 y1).
Proof. exact (SYM (@lem1324305 y1 x1)). Qed.
Lemma lem1324308 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1324294 A B x y) (@lem1324293 A B x y)). Qed.
Lemma lem1324309 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1324308 hreal hreal x y). Qed.
Lemma lem1324310 (x1 : hreal) (y1 : hreal) : (term20 x1 y1) = y1.
Proof. exact (@lem1324309 x1 y1). Qed.
Lemma lem1324311 (x1 : hreal) (y1 : hreal) : y1 = (term20 x1 y1).
Proof. exact (SYM (@lem1324310 x1 y1)). Qed.
Lemma lem1324313 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1324300 A B y x) (@lem1324299 A B x y)). Qed.
Lemma lem1324314 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1324313 hreal hreal y x). Qed.
Lemma lem1324315 (y2 : hreal) (x2 : hreal) : (term19 x2 y2) = x2.
Proof. exact (@lem1324314 y2 x2). Qed.
Lemma lem1324316 (x2 : hreal) (y2 : hreal) : x2 = (term19 x2 y2).
Proof. exact (SYM (@lem1324315 y2 x2)). Qed.
Lemma lem1324318 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1324294 A B x y) (@lem1324293 A B x y)). Qed.
Lemma lem1324319 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1324318 hreal hreal x y). Qed.
Lemma lem1324320 (x2 : hreal) (y2 : hreal) : (term20 x2 y2) = y2.
Proof. exact (@lem1324319 x2 y2). Qed.
Lemma lem1324321 (x2 : hreal) (y2 : hreal) : y2 = (term20 x2 y2).
Proof. exact (SYM (@lem1324320 x2 y2)). Qed.
Lemma lem1324322 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1324323 (x1 : hreal) (y1 : hreal) : (term22 x1) = (term23 x1 y1).
Proof. exact (MK_COMB (@lem1324322) (@lem1324306 x1 y1)). Qed.
Lemma lem1324324 (x1 : hreal) (y1 : hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1324325 (x1 : hreal) : (term25 x1) = (term25 x1).
Proof. exact (eq_refl (term25 x1)). Qed.
Lemma lem1324326 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term22 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1324325 x1) (@lem1324324 x1 y1)). Qed.
Lemma lem1324327 (x1 : hreal) : (term22 x1) = (term26 x1).
Proof. exact (eq_refl (term22 x1)). Qed.
Lemma lem1324328 : (@eq (hreal -> hreal -> hreal -> prod hreal hreal)) = (@eq (hreal -> hreal -> hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> hreal -> prod hreal hreal))). Qed.
Lemma lem1324329 (x1 : hreal) : (term25 x1) = (term27 x1).
Proof. exact (MK_COMB (@lem1324328) (@lem1324327 x1)). Qed.
Lemma lem1324330 (x1 : hreal) (y1 : hreal) : (term24 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term24 x1 y1)). Qed.
Lemma lem1324331 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term24 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1324329 x1) (@lem1324330 x1 y1)). Qed.
Lemma lem1324332 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (TRANS (@lem1324326 x1 y1) (@lem1324331 x1 y1)). Qed.
Lemma lem1324333 (x1 : hreal) (y1 : hreal) : (term26 x1) = (term24 x1 y1).
Proof. exact (EQ_MP (@lem1324332 x1 y1) (@lem1324323 x1 y1)). Qed.
Lemma lem1324334 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term29 x1 y1).
Proof. exact (MK_COMB (@lem1324333 x1 y1) (@lem1324311 x1 y1)). Qed.
Lemma lem1324335 (x1 : hreal) (y1 : hreal) : (term29 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term29 x1 y1)). Qed.
Lemma lem1324336 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term31 x1 y1).
Proof. exact (eq_refl (term31 x1 y1)). Qed.
Lemma lem1324337 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term28 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1324336 x1 y1) (@lem1324335 x1 y1)). Qed.
Lemma lem1324338 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term32 x1 y1).
Proof. exact (eq_refl (term28 x1 y1)). Qed.
Lemma lem1324339 : (@eq (hreal -> hreal -> prod hreal hreal)) = (@eq (hreal -> hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> prod hreal hreal))). Qed.
Lemma lem1324340 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term33 x1 y1).
Proof. exact (MK_COMB (@lem1324339) (@lem1324338 x1 y1)). Qed.
Lemma lem1324341 (x1 : hreal) (y1 : hreal) : (term30 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term30 x1 y1)). Qed.
Lemma lem1324342 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term30 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1324340 x1 y1) (@lem1324341 x1 y1)). Qed.
Lemma lem1324343 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (TRANS (@lem1324337 x1 y1) (@lem1324342 x1 y1)). Qed.
Lemma lem1324344 (x1 : hreal) (y1 : hreal) : (term32 x1 y1) = (term30 x1 y1).
Proof. exact (EQ_MP (@lem1324343 x1 y1) (@lem1324334 x1 y1)). Qed.
Lemma lem1324345 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term34 x1 y1 x2) = (term35 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1324344 x1 y1) (@lem1324316 x2 y2)). Qed.
Lemma lem1324346 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term35 x1 y1 x2 y2) = (term36 x1 y1 x2 y2).
Proof. exact (eq_refl (term35 x1 y1 x2 y2)). Qed.
Lemma lem1324347 (x1 : hreal) (y1 : hreal) (x2 : hreal) : (term37 x1 y1 x2) = (term37 x1 y1 x2).
Proof. exact (eq_refl (term37 x1 y1 x2)). Qed.
Lemma lem1324348 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term34 x1 y1 x2) = (term36 x1 y1 x2 y2)).
Proof. exact (MK_COMB (@lem1324347 x1 y1 x2) (@lem1324346 x1 y1 x2 y2)). Qed.
Lemma lem1324349 (x1 : hreal) (y1 : hreal) (x2 : hreal) : (term34 x1 y1 x2) = (term38 x1 y1 x2).
Proof. exact (eq_refl (term34 x1 y1 x2)). Qed.
Lemma lem1324350 : (@eq (hreal -> prod hreal hreal)) = (@eq (hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> prod hreal hreal))). Qed.
Lemma lem1324351 (x1 : hreal) (y1 : hreal) (x2 : hreal) : (term37 x1 y1 x2) = (term39 x1 y1 x2).
Proof. exact (MK_COMB (@lem1324350) (@lem1324349 x1 y1 x2)). Qed.
Lemma lem1324352 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term36 x1 y1 x2 y2) = (term36 x1 y1 x2 y2).
Proof. exact (eq_refl (term36 x1 y1 x2 y2)). Qed.
Lemma lem1324353 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term34 x1 y1 x2) = (term36 x1 y1 x2 y2)) = ((term38 x1 y1 x2) = (term36 x1 y1 x2 y2)).
Proof. exact (MK_COMB (@lem1324351 x1 y1 x2) (@lem1324352 x1 y1 x2 y2)). Qed.
Lemma lem1324354 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term38 x1 y1 x2) = (term36 x1 y1 x2 y2)).
Proof. exact (TRANS (@lem1324348 x1 y1 x2 y2) (@lem1324353 x1 y1 x2 y2)). Qed.
Lemma lem1324355 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term38 x1 y1 x2) = (term36 x1 y1 x2 y2).
Proof. exact (EQ_MP (@lem1324354 x1 y1 x2 y2) (@lem1324345 x1 y1 x2 y2)). Qed.
Lemma lem1324356 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term40 x1 y1 x2 y2) = (term41 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1324355 x1 y1 x2 y2) (@lem1324321 x2 y2)). Qed.
Lemma lem1324357 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term41 x1 y1 x2 y2) = (term10 x1 y1 x2 y2).
Proof. exact (eq_refl (term41 x1 y1 x2 y2)). Qed.
Lemma lem1324358 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term42 x1 y1 x2 y2) = (term42 x1 y1 x2 y2).
Proof. exact (eq_refl (term42 x1 y1 x2 y2)). Qed.
Lemma lem1324359 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term40 x1 y1 x2 y2) = (term41 x1 y1 x2 y2)) = ((term40 x1 y1 x2 y2) = (term10 x1 y1 x2 y2)).
Proof. exact (MK_COMB (@lem1324358 x1 y1 x2 y2) (@lem1324357 x1 y1 x2 y2)). Qed.
Lemma lem1324360 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term40 x1 y1 x2 y2) = (term43 x1 y2 y1 x2).
Proof. exact (eq_refl (term40 x1 y1 x2 y2)). Qed.
Lemma lem1324361 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1324362 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term42 x1 y1 x2 y2) = (term44 x1 y2 y1 x2).
Proof. exact (MK_COMB (@lem1324361) (@lem1324360 x1 y2 y1 x2)). Qed.
Lemma lem1324363 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term10 x1 y1 x2 y2) = (term10 x1 y1 x2 y2).
Proof. exact (eq_refl (term10 x1 y1 x2 y2)). Qed.
Lemma lem1324364 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term40 x1 y1 x2 y2) = (term10 x1 y1 x2 y2)) = ((term43 x1 y2 y1 x2) = (term10 x1 y1 x2 y2)).
Proof. exact (MK_COMB (@lem1324362 x1 y2 y1 x2) (@lem1324363 x1 y1 x2 y2)). Qed.
Lemma lem1324365 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term40 x1 y1 x2 y2) = (term41 x1 y1 x2 y2)) = ((term43 x1 y2 y1 x2) = (term10 x1 y1 x2 y2)).
Proof. exact (TRANS (@lem1324359 x1 y1 x2 y2) (@lem1324364 x1 y1 x2 y2)). Qed.
Lemma lem1324366 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term43 x1 y2 y1 x2) = (term10 x1 y1 x2 y2).
Proof. exact (EQ_MP (@lem1324365 x1 y1 x2 y2) (@lem1324356 x1 y1 x2 y2)). Qed.
Lemma lem1324367 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term10 x1 y1 x2 y2) = (term43 x1 y2 y1 x2).
Proof. exact (SYM (@lem1324366 x1 y1 x2 y2)). Qed.
Lemma lem1324368 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term9 x1 y1 x2 y2) = (term43 x1 y2 y1 x2).
Proof. exact (TRANS (@lem1324289 x1 y1 x2 y2) (@lem1324367 x1 y2 y1 x2)). Qed.
Lemma lem1324369 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term45 x1 y2 y1.
Proof. exact (fun x2 : hreal => @lem1324368 x1 y2 y1 x2). Qed.
Lemma lem1324370 (x1 : hreal) (y2 : hreal) : term46 x1 y2.
Proof. exact (fun y1 : hreal => @lem1324369 x1 y2 y1). Qed.
Lemma lem1324371 (x1 : hreal) : term47 x1.
Proof. exact (fun y2 : hreal => @lem1324370 x1 y2). Qed.
Lemma lem1324372 : term48.
Proof. exact (fun x1 : hreal => @lem1324371 x1). Qed.
