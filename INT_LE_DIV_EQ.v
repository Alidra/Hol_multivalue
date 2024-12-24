Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_DIV_EQ_term_abbrevs.
Require Import INT_DIV_LT_EQ_spec.
Require Import INT_NOT_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem2611270 (y : int) (x : int) (h1 : (term0 x y) = (int_le y x)) : (term0 x y) = (int_le y x).
Proof. exact (h1). Qed.
Lemma lem2611271 (y : int) (x : int) (h1 : (term0 x y) = (int_le y x)) : (int_le y x) = (term0 x y).
Proof. exact (SYM (@lem2611270 y x h1)). Qed.
Lemma lem2611272 (x : int) (y : int) (h1 : (int_le y x) = (term0 x y)) : (int_le y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2611273 (x : int) (y : int) (h1 : (int_le y x) = (term0 x y)) : (term0 x y) = (int_le y x).
Proof. exact (SYM (@lem2611272 x y h1)). Qed.
Lemma lem2611274 (x : int) (y : int) : ((term0 x y) = (int_le y x)) = ((int_le y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (int_le y x) => @lem2611271 y x h1) (fun h1 : (int_le y x) = (term0 x y) => @lem2611273 x y h1)). Qed.
Lemma lem2611275 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2611274 x y)). Qed.
Lemma lem2611276 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611277 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2611276) (@lem2611275 x)). Qed.
Lemma lem2611278 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2611277 x)). Qed.
Lemma lem2611279 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611280 : term7 = term8.
Proof. exact (MK_COMB (@lem2611279) (@lem2611278)). Qed.
Lemma lem2611281 : term8.
Proof. exact (EQ_MP (@lem2611280) (@lem2306785)). Qed.
Lemma lem2611282 (a : int) : term9 a.
Proof. exact (@lem2611267 a). Qed.
Lemma lem2611283 (a : int) : (term9 a) = (term10 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem2611284 (a : int) : term10 a.
Proof. exact (EQ_MP (@lem2611283 a) (@lem2611282 a)). Qed.
Lemma lem2611285 (a : int) (b : int) : term11 a b.
Proof. exact (@lem2611284 a b). Qed.
Lemma lem2611286 (b : int) (a : int) : (term11 a b) = (term12 b a).
Proof. exact (eq_refl (term11 a b)). Qed.
Lemma lem2611287 (b : int) (a : int) : term12 b a.
Proof. exact (EQ_MP (@lem2611286 b a) (@lem2611285 a b)). Qed.
Lemma lem2611288 (b : int) (a : int) (c : int) : term13 b a c.
Proof. exact (@lem2611287 b a c). Qed.
Lemma lem2611289 (b : int) (a : int) (c : int) : (term13 b a c) = (term14 b a c).
Proof. exact (eq_refl (term13 b a c)). Qed.
Lemma lem2611290 (b : int) (a : int) (c : int) : term14 b a c.
Proof. exact (EQ_MP (@lem2611289 b a c) (@lem2611288 b a c)). Qed.
Lemma lem2611291 (a : int) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem2611292 (b : int) (c : int) (a : int) (h1 : term15 a) : (term16 b a c) = (term17 b a c).
Proof. exact (@lem2611290 b a c (@lem2611291 a h1)). Qed.
Lemma lem2611298 (x : int) : term18 x.
Proof. exact (@lem2611281 x). Qed.
Lemma lem2611299 (x : int) : (term18 x) = (term4 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2611300 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2611299 x) (@lem2611298 x)). Qed.
Lemma lem2611301 (x : int) (y : int) : term19 x y.
Proof. exact (@lem2611300 x y). Qed.
Lemma lem2611302 (x : int) (y : int) : (term19 x y) = ((int_le y x) = (term0 x y)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem2611319 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2611320 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem2611319 p q p' q'). Qed.
Lemma lem2611321 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem2611320 p q p'). Qed.
Lemma lem2611322 (a : int) (c : int) (b : int) : term23 a c b.
Proof. exact (@lem2611321 (term15 a) ((term24 c b a) = (term25 a c b))). Qed.
Lemma lem2611323 (a : int) (c : int) (b : int) (p' : Prop) : term26 a c b p'.
Proof. exact (@lem2611322 a c b p'). Qed.
Lemma lem2611324 (a : int) (c : int) (b : int) (p' : Prop) : (term26 a c b p') = (term27 a c b p').
Proof. exact (eq_refl (term26 a c b p')). Qed.
Lemma lem2611325 (a : int) (c : int) (b : int) (p' : Prop) : term27 a c b p'.
Proof. exact (EQ_MP (@lem2611324 a c b p') (@lem2611323 a c b p')). Qed.
Lemma lem2611326 (a : int) (c : int) (b : int) (p' : Prop) (q' : Prop) : term28 a c b p' q'.
Proof. exact (@lem2611325 a c b p' q'). Qed.
Lemma lem2611327 (a : int) (c : int) (b : int) (p' : Prop) (q' : Prop) : (term28 a c b p' q') = (term29 a c b p' q').
Proof. exact (eq_refl (term28 a c b p' q')). Qed.
Lemma lem2611328 (a : int) (c : int) (b : int) (p' : Prop) (q' : Prop) : term29 a c b p' q'.
Proof. exact (EQ_MP (@lem2611327 a c b p' q') (@lem2611326 a c b p' q')). Qed.
Lemma lem2611329 (a : int) : (term15 a) = (term15 a).
Proof. exact (eq_refl (term15 a)). Qed.
Lemma lem2611330 (c : int) (b : int) (a : int) (q' : Prop) : term30 c b a q'.
Proof. exact (@lem2611328 a c b (term15 a) q'). Qed.
Lemma lem2611331 (c : int) (b : int) (a : int) (q' : Prop) : term31 c b a q'.
Proof. exact (@lem2611330 c b a q' (@lem2611329 a)). Qed.
Lemma lem2611332 (a : int) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem2611333 (a : int) : (term15 a) = ((term15 a) = True).
Proof. exact (@lem7 (term15 a)). Qed.
Lemma lem2611338 (x : int) (y : int) : (int_le y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2611302 x y) (@lem2611301 x y)). Qed.
Lemma lem2611339 (b : int) (a : int) (c : int) : (term24 c b a) = (term32 b a c).
Proof. exact (@lem2611338 (div b a) c). Qed.
Lemma lem2611341 (b : int) (a : int) (c : int) : term14 b a c.
Proof. exact (fun h0 : term15 a => @lem2611292 b c a h0). Qed.
Lemma lem2611343 (a : int) (h1 : term15 a) : (term15 a) = True.
Proof. exact (EQ_MP (@lem2611333 a) (@lem2611332 a h1)). Qed.
Lemma lem2611344 (a : int) (h1 : term15 a) : True = (term15 a).
Proof. exact (SYM (@lem2611343 a h1)). Qed.
Lemma lem2611345 (a : int) (h1 : term15 a) : term15 a.
Proof. exact (EQ_MP (@lem2611344 a h1) (@lem0)). Qed.
Lemma lem2611346 (b : int) (c : int) (a : int) (h1 : term15 a) : (term16 b a c) = (term17 b a c).
Proof. exact (@lem2611341 b a c (@lem2611345 a h1)). Qed.
Lemma lem2611347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2611348 (b : int) (c : int) (a : int) (h1 : term15 a) : (term32 b a c) = (term33 b a c).
Proof. exact (MK_COMB (@lem2611347) (@lem2611346 b c a h1)). Qed.
Lemma lem2611349 (b : int) (c : int) (a : int) (h1 : term15 a) : (term24 c b a) = (term33 b a c).
Proof. exact (TRANS (@lem2611339 b a c) (@lem2611348 b c a h1)). Qed.
Lemma lem2611350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2611351 (b : int) (c : int) (a : int) (h1 : term15 a) : (term34 c b a) = (term35 b a c).
Proof. exact (MK_COMB (@lem2611350) (@lem2611349 b c a h1)). Qed.
Lemma lem2611353 (x : int) (y : int) : (int_le y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2611302 x y) (@lem2611301 x y)). Qed.
Lemma lem2611354 (b : int) (a : int) (c : int) : (term25 a c b) = (term33 b a c).
Proof. exact (@lem2611353 b (int_mul a c)). Qed.
Lemma lem2611355 (b : int) (c : int) (a : int) (h1 : term15 a) : ((term24 c b a) = (term25 a c b)) = ((term33 b a c) = (term33 b a c)).
Proof. exact (MK_COMB (@lem2611351 b c a h1) (@lem2611354 b a c)). Qed.
Lemma lem2611357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2611358 (x : Prop) : (x = x) = True.
Proof. exact (@lem2611357 Prop x). Qed.
Lemma lem2611359 (b : int) (a : int) (c : int) : ((term33 b a c) = (term33 b a c)) = True.
Proof. exact (@lem2611358 (term33 b a c)). Qed.
Lemma lem2611360 (c : int) (b : int) (a : int) (h1 : term15 a) : ((term24 c b a) = (term25 a c b)) = True.
Proof. exact (TRANS (@lem2611355 b c a h1) (@lem2611359 b a c)). Qed.
Lemma lem2611361 (a : int) (c : int) (b : int) : term36 a c b.
Proof. exact (fun h0 : term15 a => @lem2611360 c b a h0). Qed.
Lemma lem2611362 (c : int) (b : int) (a : int) : term37 c b a.
Proof. exact (@lem2611331 c b a True). Qed.
Lemma lem2611363 (c : int) (b : int) (a : int) : (term38 a c b) = (term39 a).
Proof. exact (@lem2611362 c b a (@lem2611361 a c b)). Qed.
Lemma lem2611365 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2611366 (a : int) : (term39 a) = True.
Proof. exact (@lem2611365 (term15 a)). Qed.
Lemma lem2611367 (a : int) (c : int) (b : int) : (term38 a c b) = True.
Proof. exact (TRANS (@lem2611363 c b a) (@lem2611366 a)). Qed.
Lemma lem2611368 (a : int) (b : int) : (term40 a b) = term41.
Proof. exact (fun_ext (fun c : int => @lem2611367 a c b)). Qed.
Lemma lem2611369 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611370 (a : int) (b : int) : (term42 a b) = term43.
Proof. exact (MK_COMB (@lem2611369) (@lem2611368 a b)). Qed.
Lemma lem2611372 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611373 (t : Prop) : (term45 t) = t.
Proof. exact (@lem2611372 int t). Qed.
Lemma lem2611374 : term43 = True.
Proof. exact (@lem2611373 True). Qed.
Lemma lem2611375 (a : int) (b : int) : (term42 a b) = True.
Proof. exact (TRANS (@lem2611370 a b) (@lem2611374)). Qed.
Lemma lem2611376 (a : int) : (term46 a) = term41.
Proof. exact (fun_ext (fun b : int => @lem2611375 a b)). Qed.
Lemma lem2611377 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611378 (a : int) : (term47 a) = term43.
Proof. exact (MK_COMB (@lem2611377) (@lem2611376 a)). Qed.
Lemma lem2611380 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611381 (t : Prop) : (term45 t) = t.
Proof. exact (@lem2611380 int t). Qed.
Lemma lem2611382 : term43 = True.
Proof. exact (@lem2611381 True). Qed.
Lemma lem2611383 (a : int) : (term47 a) = True.
Proof. exact (TRANS (@lem2611378 a) (@lem2611382)). Qed.
Lemma lem2611384 : term48 = term41.
Proof. exact (fun_ext (fun a : int => @lem2611383 a)). Qed.
Lemma lem2611385 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611386 : term49 = term43.
Proof. exact (MK_COMB (@lem2611385) (@lem2611384)). Qed.
Lemma lem2611388 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611389 (t : Prop) : (term45 t) = t.
Proof. exact (@lem2611388 int t). Qed.
Lemma lem2611390 : term43 = True.
Proof. exact (@lem2611389 True). Qed.
Lemma lem2611391 : term49 = True.
Proof. exact (TRANS (@lem2611386) (@lem2611390)). Qed.
Lemma lem2611392 : True = term49.
Proof. exact (SYM (@lem2611391)). Qed.
Lemma lem2611393 : term49.
Proof. exact (EQ_MP (@lem2611392) (@lem0)). Qed.
