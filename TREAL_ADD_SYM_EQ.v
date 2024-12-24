Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_SYM_EQ_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import PAIR_EQ_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_add_spec.
Lemma lem1327327 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1327328 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1327329 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1327328 x) (@lem1327327 x)). Qed.
Lemma lem1327330 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1327329 x y). Qed.
Lemma lem1327331 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1327333 {A B : Type'} (x : A) : term3 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem1327334 {A B : Type'} (x : A) : (term3 A B x) = (term4 A B x).
Proof. exact (eq_refl (term3 A B x)). Qed.
Lemma lem1327335 {A B : Type'} (x : A) : term4 A B x.
Proof. exact (EQ_MP (@lem1327334 A B x) (@lem1327333 A B x)). Qed.
Lemma lem1327336 {A B : Type'} (x : A) (y : B) : term5 A B x y.
Proof. exact (@lem1327335 A B x y). Qed.
Lemma lem1327337 {A B : Type'} (x : A) (y : B) : (term5 A B x y) = (term6 A B x y).
Proof. exact (eq_refl (term5 A B x y)). Qed.
Lemma lem1327338 {A B : Type'} (x : A) (y : B) : term6 A B x y.
Proof. exact (EQ_MP (@lem1327337 A B x y) (@lem1327336 A B x y)). Qed.
Lemma lem1327339 {A B : Type'} (x : A) (y : B) (a : A) : term7 A B x y a.
Proof. exact (@lem1327338 A B x y a). Qed.
Lemma lem1327340 {A B : Type'} (x : A) (a : A) (y : B) : (term7 A B x y a) = (term8 A B x a y).
Proof. exact (eq_refl (term7 A B x y a)). Qed.
Lemma lem1327341 {A B : Type'} (x : A) (a : A) (y : B) : term8 A B x a y.
Proof. exact (EQ_MP (@lem1327340 A B x a y) (@lem1327339 A B x y a)). Qed.
Lemma lem1327342 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term9 A B x a y b.
Proof. exact (@lem1327341 A B x a y b). Qed.
Lemma lem1327343 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term9 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term10 A B x a y b)).
Proof. exact (eq_refl (term9 A B x a y b)). Qed.
Lemma lem1327345 (x1 : hreal) : term11 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1327346 (x1 : hreal) : (term11 x1) = (term12 x1).
Proof. exact (eq_refl (term11 x1)). Qed.
Lemma lem1327347 (x1 : hreal) : term12 x1.
Proof. exact (EQ_MP (@lem1327346 x1) (@lem1327345 x1)). Qed.
Lemma lem1327348 (x1 : hreal) (x2 : hreal) : term13 x1 x2.
Proof. exact (@lem1327347 x1 x2). Qed.
Lemma lem1327349 (x1 : hreal) (x2 : hreal) : (term13 x1 x2) = (term14 x1 x2).
Proof. exact (eq_refl (term13 x1 x2)). Qed.
Lemma lem1327350 (x1 : hreal) (x2 : hreal) : term14 x1 x2.
Proof. exact (EQ_MP (@lem1327349 x1 x2) (@lem1327348 x1 x2)). Qed.
Lemma lem1327351 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term15 x1 x2 y1.
Proof. exact (@lem1327350 x1 x2 y1). Qed.
Lemma lem1327352 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term15 x1 x2 y1) = (term16 x1 x2 y1).
Proof. exact (eq_refl (term15 x1 x2 y1)). Qed.
Lemma lem1327353 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term16 x1 x2 y1.
Proof. exact (EQ_MP (@lem1327352 x1 x2 y1) (@lem1327351 x1 x2 y1)). Qed.
Lemma lem1327354 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term17 x1 x2 y1 y2.
Proof. exact (@lem1327353 x1 x2 y1 y2). Qed.
Lemma lem1327355 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term17 x1 x2 y1 y2) = ((term18 x1 y1 x2 y2) = (term19 x1 x2 y1 y2)).
Proof. exact (eq_refl (term17 x1 x2 y1 y2)). Qed.
Lemma lem1327357 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term20 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1327358 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = ((term21 _5106 _5107 P) = (term22 _5106 _5107 P)).
Proof. exact (eq_refl (term20 _5106 _5107 P)). Qed.
Lemma lem1327365 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term22 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327358 _5106 _5107 P) (@lem1327357 _5106 _5107 P)). Qed.
Lemma lem1327366 (P : type1233) : (term23 P) = (term24 P).
Proof. exact (@lem1327365 hreal hreal P). Qed.
Lemma lem1327367 : term25 = term26.
Proof. exact (@lem1327366 term27). Qed.
Lemma lem1327368 (x : prod hreal hreal) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1327369 : term30 = term27.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1327368 x)). Qed.
Lemma lem1327370 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327371 : term25 = term31.
Proof. exact (MK_COMB (@lem1327370) (@lem1327369)). Qed.
Lemma lem1327372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327373 : term32 = term33.
Proof. exact (MK_COMB (@lem1327372) (@lem1327371)). Qed.
Lemma lem1327374 (p1 : hreal) (p2 : hreal) : (term34 p1 p2) = (term35 p1 p2).
Proof. exact (eq_refl (term34 p1 p2)). Qed.
Lemma lem1327375 (p1 : hreal) : (term36 p1) = (term37 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1327374 p1 p2)). Qed.
Lemma lem1327376 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327377 (p1 : hreal) : (term38 p1) = (term39 p1).
Proof. exact (MK_COMB (@lem1327376) (@lem1327375 p1)). Qed.
Lemma lem1327378 : term40 = term41.
Proof. exact (fun_ext (fun p1 : hreal => @lem1327377 p1)). Qed.
Lemma lem1327379 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327380 : term26 = term42.
Proof. exact (MK_COMB (@lem1327379) (@lem1327378)). Qed.
Lemma lem1327381 : (term25 = term26) = (term31 = term42).
Proof. exact (MK_COMB (@lem1327373) (@lem1327380)). Qed.
Lemma lem1327382 : term31 = term42.
Proof. exact (EQ_MP (@lem1327381) (@lem1327367)). Qed.
Lemma lem1327400 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term22 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327358 _5106 _5107 P) (@lem1327357 _5106 _5107 P)). Qed.
Lemma lem1327401 (P : type1233) : (term23 P) = (term24 P).
Proof. exact (@lem1327400 hreal hreal P). Qed.
Lemma lem1327402 (p1 : hreal) (p2 : hreal) : (term43 p1 p2) = (term44 p1 p2).
Proof. exact (@lem1327401 (term45 p1 p2)). Qed.
Lemma lem1327403 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term46 p1 p2 y) = ((term47 p1 p2 y) = (term48 y p1 p2)).
Proof. exact (eq_refl (term46 p1 p2 y)). Qed.
Lemma lem1327404 (p1 : hreal) (p2 : hreal) : (term49 p1 p2) = (term45 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1327403 y p1 p2)). Qed.
Lemma lem1327405 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327406 (p1 : hreal) (p2 : hreal) : (term43 p1 p2) = (term35 p1 p2).
Proof. exact (MK_COMB (@lem1327405) (@lem1327404 p1 p2)). Qed.
Lemma lem1327407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327408 (p1 : hreal) (p2 : hreal) : (term50 p1 p2) = (term51 p1 p2).
Proof. exact (MK_COMB (@lem1327407) (@lem1327406 p1 p2)). Qed.
Lemma lem1327409 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term52 p1 p2 p1' p2') = ((term18 p1 p2 p1' p2') = (term18 p1' p2' p1 p2)).
Proof. exact (eq_refl (term52 p1 p2 p1' p2')). Qed.
Lemma lem1327410 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term53 p1 p2 p1') = (term54 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1327409 p1' p2' p1 p2)). Qed.
Lemma lem1327411 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327412 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term55 p1 p2 p1') = (term56 p1' p1 p2).
Proof. exact (MK_COMB (@lem1327411) (@lem1327410 p1' p1 p2)). Qed.
Lemma lem1327413 (p1 : hreal) (p2 : hreal) : (term57 p1 p2) = (term58 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1327412 p1' p1 p2)). Qed.
Lemma lem1327414 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327415 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term59 p1 p2).
Proof. exact (MK_COMB (@lem1327414) (@lem1327413 p1 p2)). Qed.
Lemma lem1327416 (p1 : hreal) (p2 : hreal) : ((term43 p1 p2) = (term44 p1 p2)) = ((term35 p1 p2) = (term59 p1 p2)).
Proof. exact (MK_COMB (@lem1327408 p1 p2) (@lem1327415 p1 p2)). Qed.
Lemma lem1327417 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = (term59 p1 p2).
Proof. exact (EQ_MP (@lem1327416 p1 p2) (@lem1327402 p1 p2)). Qed.
Lemma lem1327433 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term18 x1 y1 x2 y2) = (term19 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327355 x1 x2 y1 y2) (@lem1327354 x1 x2 y1 y2)). Qed.
Lemma lem1327434 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term18 p1 p2 p1' p2') = (term19 p1 p1' p2 p2').
Proof. exact (@lem1327433 p1 p1' p2 p2'). Qed.
Lemma lem1327441 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1327442 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term60 p1 p2 p1' p2') = (term61 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1327441) (@lem1327434 p1 p1' p2 p2')). Qed.
Lemma lem1327444 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term18 x1 y1 x2 y2) = (term19 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327355 x1 x2 y1 y2) (@lem1327354 x1 x2 y1 y2)). Qed.
Lemma lem1327445 (p1' : hreal) (p1 : hreal) (p2' : hreal) (p2 : hreal) : (term18 p1' p2' p1 p2) = (term19 p1' p1 p2' p2).
Proof. exact (@lem1327444 p1' p1 p2' p2). Qed.
Lemma lem1327447 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1327331 y x) (@lem1327330 x y)). Qed.
Lemma lem1327448 (p1 : hreal) (p1' : hreal) : (hreal_add p1' p1) = (hreal_add p1 p1').
Proof. exact (@lem1327447 p1 p1'). Qed.
Lemma lem1327452 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1327453 (p1 : hreal) (p1' : hreal) : (term62 p1' p1) = (term62 p1 p1').
Proof. exact (MK_COMB (@lem1327452) (@lem1327448 p1 p1')). Qed.
Lemma lem1327455 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1327331 y x) (@lem1327330 x y)). Qed.
Lemma lem1327456 (p2 : hreal) (p2' : hreal) : (hreal_add p2' p2) = (hreal_add p2 p2').
Proof. exact (@lem1327455 p2 p2'). Qed.
Lemma lem1327460 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term19 p1' p1 p2' p2) = (term19 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1327453 p1 p1') (@lem1327456 p2 p2')). Qed.
Lemma lem1327461 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term18 p1' p2' p1 p2) = (term19 p1 p1' p2 p2').
Proof. exact (TRANS (@lem1327445 p1' p1 p2' p2) (@lem1327460 p1 p1' p2 p2')). Qed.
Lemma lem1327462 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : ((term18 p1 p2 p1' p2') = (term18 p1' p2' p1 p2)) = ((term19 p1 p1' p2 p2') = (term19 p1 p1' p2 p2')).
Proof. exact (MK_COMB (@lem1327442 p1 p1' p2 p2') (@lem1327461 p1 p1' p2 p2')). Qed.
Lemma lem1327464 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term10 A B x a y b).
Proof. exact (EQ_MP (@lem1327343 A B x a y b) (@lem1327342 A B x a y b)). Qed.
Lemma lem1327465 (x : hreal) (a : hreal) (y : hreal) (b : hreal) : ((@pair hreal hreal x y) = (@pair hreal hreal a b)) = (term63 x a y b).
Proof. exact (@lem1327464 hreal hreal x a y b). Qed.
Lemma lem1327466 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : ((term19 p1 p1' p2 p2') = (term19 p1 p1' p2 p2')) = (term64 p1 p1' p2 p2').
Proof. exact (@lem1327465 (hreal_add p1 p1') (hreal_add p1 p1') (hreal_add p2 p2') (hreal_add p2 p2')). Qed.
Lemma lem1327470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327471 (x : hreal) : (x = x) = True.
Proof. exact (@lem1327470 hreal x). Qed.
Lemma lem1327472 (p1 : hreal) (p1' : hreal) : ((hreal_add p1 p1') = (hreal_add p1 p1')) = True.
Proof. exact (@lem1327471 (hreal_add p1 p1')). Qed.
Lemma lem1327473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1327474 (p1 : hreal) (p1' : hreal) : (term65 p1 p1') = (and True).
Proof. exact (MK_COMB (@lem1327473) (@lem1327472 p1 p1')). Qed.
Lemma lem1327476 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327477 (x : hreal) : (x = x) = True.
Proof. exact (@lem1327476 hreal x). Qed.
Lemma lem1327478 (p2 : hreal) (p2' : hreal) : ((hreal_add p2 p2') = (hreal_add p2 p2')) = True.
Proof. exact (@lem1327477 (hreal_add p2 p2')). Qed.
Lemma lem1327479 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term64 p1 p1' p2 p2') = (True /\ True).
Proof. exact (MK_COMB (@lem1327474 p1 p1') (@lem1327478 p2 p2')). Qed.
Lemma lem1327481 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1327482 : (True /\ True) = True.
Proof. exact (@lem1327481 True). Qed.
Lemma lem1327483 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term64 p1 p1' p2 p2') = True.
Proof. exact (TRANS (@lem1327479 p1 p1' p2 p2') (@lem1327482)). Qed.
Lemma lem1327484 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : ((term19 p1 p1' p2 p2') = (term19 p1 p1' p2 p2')) = True.
Proof. exact (TRANS (@lem1327466 p1 p1' p2 p2') (@lem1327483 p1 p1' p2 p2')). Qed.
Lemma lem1327485 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term18 p1 p2 p1' p2') = (term18 p1' p2' p1 p2)) = True.
Proof. exact (TRANS (@lem1327462 p1 p1' p2 p2') (@lem1327484 p1 p1' p2 p2')). Qed.
Lemma lem1327486 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term54 p1' p1 p2) = term66.
Proof. exact (fun_ext (fun p2' : hreal => @lem1327485 p1' p2' p1 p2)). Qed.
Lemma lem1327487 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327488 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term56 p1' p1 p2) = term67.
Proof. exact (MK_COMB (@lem1327487) (@lem1327486 p1' p1 p2)). Qed.
Lemma lem1327490 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327491 (t : Prop) : (term69 t) = t.
Proof. exact (@lem1327490 hreal t). Qed.
Lemma lem1327492 : term67 = True.
Proof. exact (@lem1327491 True). Qed.
Lemma lem1327493 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term56 p1' p1 p2) = True.
Proof. exact (TRANS (@lem1327488 p1' p1 p2) (@lem1327492)). Qed.
Lemma lem1327494 (p1 : hreal) (p2 : hreal) : (term58 p1 p2) = term66.
Proof. exact (fun_ext (fun p1' : hreal => @lem1327493 p1' p1 p2)). Qed.
Lemma lem1327495 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327496 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = term67.
Proof. exact (MK_COMB (@lem1327495) (@lem1327494 p1 p2)). Qed.
Lemma lem1327498 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327499 (t : Prop) : (term69 t) = t.
Proof. exact (@lem1327498 hreal t). Qed.
Lemma lem1327500 : term67 = True.
Proof. exact (@lem1327499 True). Qed.
Lemma lem1327501 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = True.
Proof. exact (TRANS (@lem1327496 p1 p2) (@lem1327500)). Qed.
Lemma lem1327502 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = True.
Proof. exact (TRANS (@lem1327417 p1 p2) (@lem1327501 p1 p2)). Qed.
Lemma lem1327503 (p1 : hreal) : (term37 p1) = term66.
Proof. exact (fun_ext (fun p2 : hreal => @lem1327502 p1 p2)). Qed.
Lemma lem1327504 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327505 (p1 : hreal) : (term39 p1) = term67.
Proof. exact (MK_COMB (@lem1327504) (@lem1327503 p1)). Qed.
Lemma lem1327507 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327508 (t : Prop) : (term69 t) = t.
Proof. exact (@lem1327507 hreal t). Qed.
Lemma lem1327509 : term67 = True.
Proof. exact (@lem1327508 True). Qed.
Lemma lem1327510 (p1 : hreal) : (term39 p1) = True.
Proof. exact (TRANS (@lem1327505 p1) (@lem1327509)). Qed.
Lemma lem1327511 : term41 = term66.
Proof. exact (fun_ext (fun p1 : hreal => @lem1327510 p1)). Qed.
Lemma lem1327512 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327513 : term42 = term67.
Proof. exact (MK_COMB (@lem1327512) (@lem1327511)). Qed.
Lemma lem1327515 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327516 (t : Prop) : (term69 t) = t.
Proof. exact (@lem1327515 hreal t). Qed.
Lemma lem1327517 : term67 = True.
Proof. exact (@lem1327516 True). Qed.
Lemma lem1327518 : term42 = True.
Proof. exact (TRANS (@lem1327513) (@lem1327517)). Qed.
Lemma lem1327519 : term31 = True.
Proof. exact (TRANS (@lem1327382) (@lem1327518)). Qed.
Lemma lem1327520 : True = term31.
Proof. exact (SYM (@lem1327519)). Qed.
Lemma lem1327521 : term31.
Proof. exact (EQ_MP (@lem1327520) (@lem0)). Qed.
