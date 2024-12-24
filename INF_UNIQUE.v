Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_UNIQUE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_EQ_spec.
Require Import INF_SING_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem5273354 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem5273355 (s : real -> Prop) (h1 : term0) : term1 s.
Proof. exact (@lem5273354 h1 s). Qed.
Lemma lem5273356 (s : real -> Prop) : (term1 s) = (term2 s).
Proof. exact (eq_refl (term1 s)). Qed.
Lemma lem5273357 (s : real -> Prop) (h1 : term0) : term2 s.
Proof. exact (EQ_MP (@lem5273356 s) (@lem5273355 s h1)). Qed.
Lemma lem5273358 (s : real -> Prop) (t : real -> Prop) (h1 : term0) : term3 s t.
Proof. exact (@lem5273357 s h1 t). Qed.
Lemma lem5273359 (s : real -> Prop) (t : real -> Prop) : (term3 s t) = (term4 s t).
Proof. exact (eq_refl (term3 s t)). Qed.
Lemma lem5273360 (s : real -> Prop) (t : real -> Prop) (h1 : term0) : term4 s t.
Proof. exact (EQ_MP (@lem5273359 s t) (@lem5273358 s t h1)). Qed.
Lemma lem5273361 (s : real -> Prop) (t : real -> Prop) (h1 : term5 s t) : term5 s t.
Proof. exact (h1). Qed.
Lemma lem5273362 (s : real -> Prop) (t : real -> Prop) (h1 : term0) (h2 : term5 s t) : (inf s) = (inf t).
Proof. exact (@lem5273360 s t h1 (@lem5273361 s t h2)). Qed.
Lemma lem5273363 (s : real -> Prop) (t : real -> Prop) (h1 : term5 s t) : term6 s t.
Proof. exact (fun h0 : term0 => @lem5273362 s t h0 h1). Qed.
Lemma lem5273364 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem5273365 (s : real -> Prop) (t : real -> Prop) (h1 : term0) (h2 : term5 s t) : (inf s) = (inf t).
Proof. exact (@lem5273363 s t h2 (@lem5273364 h1)). Qed.
Lemma lem5273366 (s : real -> Prop) (t : real -> Prop) (h1 : term0) : term4 s t.
Proof. exact (fun h0 : term5 s t => @lem5273365 s t h1 h0). Qed.
Lemma lem5273367 (s : real -> Prop) (h1 : term0) : term2 s.
Proof. exact (fun t : real -> Prop => @lem5273366 s t h1). Qed.
Lemma lem5273368 (h1 : term0) : term0.
Proof. exact (fun s : real -> Prop => @lem5273367 s h1). Qed.
Lemma lem5273369 : term7.
Proof. exact (fun h0 : term0 => @lem5273368 h0). Qed.
Lemma lem5273370 : term0.
Proof. exact (@lem5273369 (@lem5205408)). Qed.
Lemma lem5273371 (s : real -> Prop) : term1 s.
Proof. exact (@lem5273370 s). Qed.
Lemma lem5273372 (s : real -> Prop) : (term1 s) = (term2 s).
Proof. exact (eq_refl (term1 s)). Qed.
Lemma lem5273373 (s : real -> Prop) : term2 s.
Proof. exact (EQ_MP (@lem5273372 s) (@lem5273371 s)). Qed.
Lemma lem5273374 (s : real -> Prop) (t : real -> Prop) : term3 s t.
Proof. exact (@lem5273373 s t). Qed.
Lemma lem5273375 (s : real -> Prop) (t : real -> Prop) : (term3 s t) = (term4 s t).
Proof. exact (eq_refl (term3 s t)). Qed.
Lemma lem5273378 (a : real) (h1 : (term8 a) = a) : (term8 a) = a.
Proof. exact (h1). Qed.
Lemma lem5273379 (a : real) (h1 : (term8 a) = a) : a = (term8 a).
Proof. exact (SYM (@lem5273378 a h1)). Qed.
Lemma lem5273380 (a : real) (h1 : a = (term8 a)) : a = (term8 a).
Proof. exact (h1). Qed.
Lemma lem5273381 (a : real) (h1 : a = (term8 a)) : (term8 a) = a.
Proof. exact (SYM (@lem5273380 a h1)). Qed.
Lemma lem5273382 (a : real) : ((term8 a) = a) = (a = (term8 a)).
Proof. exact (prop_ext (fun h1 : (term8 a) = a => @lem5273379 a h1) (fun h1 : a = (term8 a) => @lem5273381 a h1)). Qed.
Lemma lem5273383 : term9 = term10.
Proof. exact (fun_ext (fun a : real => @lem5273382 a)). Qed.
Lemma lem5273384 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273385 : term11 = term12.
Proof. exact (MK_COMB (@lem5273384) (@lem5273383)). Qed.
Lemma lem5273386 : term12.
Proof. exact (EQ_MP (@lem5273385) (@lem5256827)). Qed.
Lemma lem5273387 (a : real) : term13 a.
Proof. exact (@lem5273386 a). Qed.
Lemma lem5273388 (a : real) : (term13 a) = (a = (term8 a)).
Proof. exact (eq_refl (term13 a)). Qed.
Lemma lem5273390 (s : real -> Prop) (b : real) (h1 : term14 s b) : term14 s b.
Proof. exact (h1). Qed.
Lemma lem5273392 (a : real) : a = (term8 a).
Proof. exact (EQ_MP (@lem5273388 a) (@lem5273387 a)). Qed.
Lemma lem5273393 (b : real) : b = (term8 b).
Proof. exact (@lem5273392 b). Qed.
Lemma lem5273394 (s : real -> Prop) : (term15 s) = (term15 s).
Proof. exact (eq_refl (term15 s)). Qed.
Lemma lem5273395 (s : real -> Prop) (b : real) : ((inf s) = b) = ((inf s) = (term8 b)).
Proof. exact (MK_COMB (@lem5273394 s) (@lem5273393 b)). Qed.
Lemma lem5273396 (s : real -> Prop) (b : real) : ((inf s) = (term8 b)) = ((inf s) = b).
Proof. exact (SYM (@lem5273395 s b)). Qed.
Lemma lem5273398 (s : real -> Prop) (t : real -> Prop) : term4 s t.
Proof. exact (EQ_MP (@lem5273375 s t) (@lem5273374 s t)). Qed.
Lemma lem5273399 (s : real -> Prop) (b : real) : term16 s b.
Proof. exact (@lem5273398 s (@INSERT real b (@EMPTY real))). Qed.
Lemma lem5273400 (t1 : Prop) : term17 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5273401 (t1 : Prop) : (term17 t1) = (term18 t1).
Proof. exact (eq_refl (term17 t1)). Qed.
Lemma lem5273402 (t1 : Prop) : term18 t1.
Proof. exact (EQ_MP (@lem5273401 t1) (@lem5273400 t1)). Qed.
Lemma lem5273403 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (@lem5273402 t1 t2). Qed.
Lemma lem5273404 (t1 : Prop) (t2 : Prop) : (term19 t1 t2) = (term20 t1 t2).
Proof. exact (eq_refl (term19 t1 t2)). Qed.
Lemma lem5273405 (t1 : Prop) (t2 : Prop) : term20 t1 t2.
Proof. exact (EQ_MP (@lem5273404 t1 t2) (@lem5273403 t1 t2)). Qed.
Lemma lem5273406 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term21 t1 t2 t3.
Proof. exact (@lem5273405 t1 t2 t3). Qed.
Lemma lem5273407 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = ((term22 t1 t2 t3) = (term23 t1 t2 t3)).
Proof. exact (eq_refl (term21 t1 t2 t3)). Qed.
Lemma lem5273408 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term23 t1 t2 t3).
Proof. exact (EQ_MP (@lem5273407 t1 t2 t3) (@lem5273406 t1 t2 t3)). Qed.
Lemma lem5273409 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term23 t1 t2 t3) = (term22 t1 t2 t3).
Proof. exact (SYM (@lem5273408 t1 t2 t3)). Qed.
Lemma lem5273463 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5273464 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5273463 real P x). Qed.
Lemma lem5273465 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5273464 s x). Qed.
Lemma lem5273466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273467 (s : real -> Prop) (x : real) : (term24 x s) = (term25 s x).
Proof. exact (MK_COMB (@lem5273466) (@lem5273465 s x)). Qed.
Lemma lem5273468 (c : real) (x : real) : (real_le c x) = (real_le c x).
Proof. exact (eq_refl (real_le c x)). Qed.
Lemma lem5273469 (s : real -> Prop) (c : real) (x : real) : (term26 s c x) = (term27 s c x).
Proof. exact (MK_COMB (@lem5273467 s x) (@lem5273468 c x)). Qed.
Lemma lem5273472 (s : real -> Prop) (c : real) : (term28 s c) = (term29 s c).
Proof. exact (fun_ext (fun x : real => @lem5273469 s c x)). Qed.
Lemma lem5273473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273474 (s : real -> Prop) (c : real) : (term30 s c) = (term31 s c).
Proof. exact (MK_COMB (@lem5273473) (@lem5273472 s c)). Qed.
Lemma lem5273479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5273480 (s : real -> Prop) (c : real) : (term32 s c) = (term33 s c).
Proof. exact (MK_COMB (@lem5273479) (@lem5273474 s c)). Qed.
Lemma lem5273481 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5273482 (s : real -> Prop) (c : real) (b : real) : ((term30 s c) = (real_le c b)) = ((term31 s c) = (real_le c b)).
Proof. exact (MK_COMB (@lem5273480 s c) (@lem5273481 c b)). Qed.
Lemma lem5273485 (s : real -> Prop) (b : real) : (term34 s b) = (term35 s b).
Proof. exact (fun_ext (fun c : real => @lem5273482 s c b)). Qed.
Lemma lem5273486 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273487 (s : real -> Prop) (b : real) : (term14 s b) = (term36 s b).
Proof. exact (MK_COMB (@lem5273486) (@lem5273485 s b)). Qed.
Lemma lem5273492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273493 (s : real -> Prop) (b : real) : (term37 s b) = (term38 s b).
Proof. exact (MK_COMB (@lem5273492) (@lem5273487 s b)). Qed.
Lemma lem5273507 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5273508 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5273507 real P x). Qed.
Lemma lem5273509 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5273508 s x). Qed.
Lemma lem5273510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273511 (s : real -> Prop) (x : real) : (term24 x s) = (term25 s x).
Proof. exact (MK_COMB (@lem5273510) (@lem5273509 s x)). Qed.
Lemma lem5273512 (a : real) (x : real) : (real_le a x) = (real_le a x).
Proof. exact (eq_refl (real_le a x)). Qed.
Lemma lem5273513 (s : real -> Prop) (a : real) (x : real) : (term26 s a x) = (term27 s a x).
Proof. exact (MK_COMB (@lem5273511 s x) (@lem5273512 a x)). Qed.
Lemma lem5273516 (s : real -> Prop) (a : real) : (term28 s a) = (term29 s a).
Proof. exact (fun_ext (fun x : real => @lem5273513 s a x)). Qed.
Lemma lem5273517 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273518 (s : real -> Prop) (a : real) : (term30 s a) = (term31 s a).
Proof. exact (MK_COMB (@lem5273517) (@lem5273516 s a)). Qed.
Lemma lem5273523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5273524 (s : real -> Prop) (a : real) : (term32 s a) = (term33 s a).
Proof. exact (MK_COMB (@lem5273523) (@lem5273518 s a)). Qed.
Lemma lem5273532 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term39 A x y s) = (term40 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5273533 (y : real) (x : real) (s : real -> Prop) : (term41 x y s) = (term42 y x s).
Proof. exact (@lem5273532 real y x s). Qed.
Lemma lem5273534 (b : real) (x : real) : (term43 x b) = (term44 b x).
Proof. exact (@lem5273533 b x (@EMPTY real)). Qed.
Lemma lem5273540 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5273541 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5273540 real x). Qed.
Lemma lem5273542 (x : real) (b : real) : (term45 x b) = (term45 x b).
Proof. exact (eq_refl (term45 x b)). Qed.
Lemma lem5273543 (x : real) (b : real) : (term44 b x) = (term46 x b).
Proof. exact (MK_COMB (@lem5273542 x b) (@lem5273541 x)). Qed.
Lemma lem5273545 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5273546 (x : real) (b : real) : (term46 x b) = (x = b).
Proof. exact (@lem5273545 (x = b)). Qed.
Lemma lem5273549 (x : real) (b : real) : (term44 b x) = (x = b).
Proof. exact (TRANS (@lem5273543 x b) (@lem5273546 x b)). Qed.
Lemma lem5273550 (x : real) (b : real) : (term43 x b) = (x = b).
Proof. exact (TRANS (@lem5273534 b x) (@lem5273549 x b)). Qed.
Lemma lem5273551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273552 (x : real) (b : real) : (term47 x b) = (term48 x b).
Proof. exact (MK_COMB (@lem5273551) (@lem5273550 x b)). Qed.
Lemma lem5273553 (a : real) (x : real) : (real_le a x) = (real_le a x).
Proof. exact (eq_refl (real_le a x)). Qed.
Lemma lem5273554 (b : real) (a : real) (x : real) : (term49 b a x) = (term50 b a x).
Proof. exact (MK_COMB (@lem5273552 x b) (@lem5273553 a x)). Qed.
Lemma lem5273559 (b : real) (a : real) : (term51 b a) = (term52 b a).
Proof. exact (fun_ext (fun x : real => @lem5273554 b a x)). Qed.
Lemma lem5273560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273561 (b : real) (a : real) : (term53 b a) = (term54 b a).
Proof. exact (MK_COMB (@lem5273560) (@lem5273559 b a)). Qed.
Lemma lem5273566 (s : real -> Prop) (b : real) (a : real) : ((term30 s a) = (term53 b a)) = ((term31 s a) = (term54 b a)).
Proof. exact (MK_COMB (@lem5273524 s a) (@lem5273561 b a)). Qed.
Lemma lem5273569 (s : real -> Prop) (b : real) : (term55 s b) = (term56 s b).
Proof. exact (fun_ext (fun a : real => @lem5273566 s b a)). Qed.
Lemma lem5273570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273571 (s : real -> Prop) (b : real) : (term57 s b) = (term58 s b).
Proof. exact (MK_COMB (@lem5273570) (@lem5273569 s b)). Qed.
Lemma lem5273576 (s : real -> Prop) (b : real) : (term59 s b) = (term60 s b).
Proof. exact (MK_COMB (@lem5273493 s b) (@lem5273571 s b)). Qed.
Lemma lem5273579 (s : real -> Prop) (b : real) : (term60 s b) = (term59 s b).
Proof. exact (SYM (@lem5273576 s b)). Qed.
Lemma lem5273581 (p : Prop) : p = (term61 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5273582 (s : real -> Prop) (b : real) : (term60 s b) = (term62 s b).
Proof. exact (@lem5273581 (term60 s b)). Qed.
Lemma lem5273583 (s : real -> Prop) (b : real) : (term62 s b) = (term60 s b).
Proof. exact (SYM (@lem5273582 s b)). Qed.
Lemma lem5273584 (s : real -> Prop) (b : real) (h1 : term63 s b) : term63 s b.
Proof. exact (h1). Qed.
Lemma lem5273587 (s : real -> Prop) (b : real) (h1 : term62 s b) : term62 s b.
Proof. exact (h1). Qed.
Lemma lem5273588 (s : real -> Prop) (b : real) : term64 s b.
Proof. exact (fun h0 : term62 s b => @lem5273587 s b h0). Qed.
Lemma lem5273589 (s : real -> Prop) (b : real) (h1 : term64 s b) : term64 s b.
Proof. exact (h1). Qed.
Lemma lem5273590 (s : real -> Prop) (b : real) (h1 : term62 s b) : term62 s b.
Proof. exact (h1). Qed.
Lemma lem5273591 (s : real -> Prop) (b : real) (h1 : term62 s b) (h2 : term64 s b) : term62 s b.
Proof. exact (@lem5273589 s b h2 (@lem5273590 s b h1)). Qed.
Lemma lem5273592 (s : real -> Prop) (b : real) (h1 : term62 s b) : term65 s b.
Proof. exact (fun h0 : term64 s b => @lem5273591 s b h1 h0). Qed.
Lemma lem5273593 (s : real -> Prop) (b : real) (h1 : term64 s b) : term64 s b.
Proof. exact (h1). Qed.
Lemma lem5273594 (s : real -> Prop) (b : real) (h1 : term62 s b) (h2 : term64 s b) : term62 s b.
Proof. exact (@lem5273592 s b h1 (@lem5273593 s b h2)). Qed.
Lemma lem5273595 (s : real -> Prop) (b : real) (h1 : term64 s b) : term64 s b.
Proof. exact (fun h0 : term62 s b => @lem5273594 s b h0 h1). Qed.
Lemma lem5273596 (s : real -> Prop) (b : real) : term66 s b.
Proof. exact (fun h0 : term64 s b => @lem5273595 s b h0). Qed.
Lemma lem5273599 (s : real -> Prop) (b : real) : term64 s b.
Proof. exact (@lem5273596 s b (@lem5273588 s b)). Qed.
Lemma lem5273609 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5273610 (s : real -> Prop) (b : real) : (term62 s b) = (term67 s b).
Proof. exact (@lem5273609 (term63 s b)). Qed.
Lemma lem5273612 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5273613 (s : real -> Prop) (b : real) : (term67 s b) = (term60 s b).
Proof. exact (@lem5273612 (term60 s b)). Qed.
Lemma lem5273616 (s : real -> Prop) (b : real) : (term62 s b) = (term60 s b).
Proof. exact (TRANS (@lem5273610 s b) (@lem5273613 s b)). Qed.
Lemma lem5273643 (b : real) : (term69 b) = (term70 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5273616 s b)). Qed.
Lemma lem5273644 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5273645 (b : real) : (term71 b) = (term72 b).
Proof. exact (MK_COMB (@lem5273644) (@lem5273643 b)). Qed.
Lemma lem5273650 : term73 = term74.
Proof. exact (fun_ext (fun b : real => @lem5273645 b)). Qed.
Lemma lem5273651 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273660 : term75 = term76.
Proof. exact (MK_COMB (@lem5273651) (@lem5273650)). Qed.
Lemma lem5273665 (b : real) (a : real) (x : real) : (term50 b a x) = (term50 b a x).
Proof. exact (eq_refl (term50 b a x)). Qed.
Lemma lem5273666 (b : real) (a : real) : (term52 b a) = (term52 b a).
Proof. exact (fun_ext (fun x : real => @lem5273665 b a x)). Qed.
Lemma lem5273667 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273668 (b : real) (a : real) : (term54 b a) = (term54 b a).
Proof. exact (MK_COMB (@lem5273667) (@lem5273666 b a)). Qed.
Lemma lem5273673 (s : real -> Prop) (a : real) (x : real) : (term27 s a x) = (term27 s a x).
Proof. exact (eq_refl (term27 s a x)). Qed.
Lemma lem5273674 (s : real -> Prop) (a : real) : (term29 s a) = (term29 s a).
Proof. exact (fun_ext (fun x : real => @lem5273673 s a x)). Qed.
Lemma lem5273675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273676 (s : real -> Prop) (a : real) : (term31 s a) = (term31 s a).
Proof. exact (MK_COMB (@lem5273675) (@lem5273674 s a)). Qed.
Lemma lem5273677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5273678 (s : real -> Prop) (a : real) : (term33 s a) = (term33 s a).
Proof. exact (MK_COMB (@lem5273677) (@lem5273676 s a)). Qed.
Lemma lem5273679 (s : real -> Prop) (b : real) (a : real) : ((term31 s a) = (term54 b a)) = ((term31 s a) = (term54 b a)).
Proof. exact (MK_COMB (@lem5273678 s a) (@lem5273668 b a)). Qed.
Lemma lem5273680 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (fun_ext (fun a : real => @lem5273679 s b a)). Qed.
Lemma lem5273681 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273682 (s : real -> Prop) (b : real) : (term58 s b) = (term58 s b).
Proof. exact (MK_COMB (@lem5273681) (@lem5273680 s b)). Qed.
Lemma lem5273683 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5273688 (s : real -> Prop) (c : real) (x : real) : (term27 s c x) = (term27 s c x).
Proof. exact (eq_refl (term27 s c x)). Qed.
Lemma lem5273689 (s : real -> Prop) (c : real) : (term29 s c) = (term29 s c).
Proof. exact (fun_ext (fun x : real => @lem5273688 s c x)). Qed.
Lemma lem5273690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273691 (s : real -> Prop) (c : real) : (term31 s c) = (term31 s c).
Proof. exact (MK_COMB (@lem5273690) (@lem5273689 s c)). Qed.
Lemma lem5273692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5273693 (s : real -> Prop) (c : real) : (term33 s c) = (term33 s c).
Proof. exact (MK_COMB (@lem5273692) (@lem5273691 s c)). Qed.
Lemma lem5273694 (s : real -> Prop) (c : real) (b : real) : ((term31 s c) = (real_le c b)) = ((term31 s c) = (real_le c b)).
Proof. exact (MK_COMB (@lem5273693 s c) (@lem5273683 c b)). Qed.
Lemma lem5273695 (s : real -> Prop) (b : real) : (term35 s b) = (term35 s b).
Proof. exact (fun_ext (fun c : real => @lem5273694 s c b)). Qed.
Lemma lem5273696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273697 (s : real -> Prop) (b : real) : (term36 s b) = (term36 s b).
Proof. exact (MK_COMB (@lem5273696) (@lem5273695 s b)). Qed.
Lemma lem5273698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273699 (s : real -> Prop) (b : real) : (term38 s b) = (term38 s b).
Proof. exact (MK_COMB (@lem5273698) (@lem5273697 s b)). Qed.
Lemma lem5273700 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (MK_COMB (@lem5273699 s b) (@lem5273682 s b)). Qed.
Lemma lem5273701 (b : real) : (term70 b) = (term70 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5273700 s b)). Qed.
Lemma lem5273702 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5273703 (b : real) : (term72 b) = (term72 b).
Proof. exact (MK_COMB (@lem5273702) (@lem5273701 b)). Qed.
Lemma lem5273704 : term74 = term74.
Proof. exact (fun_ext (fun b : real => @lem5273703 b)). Qed.
Lemma lem5273705 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273706 : term76 = term76.
Proof. exact (MK_COMB (@lem5273705) (@lem5273704)). Qed.
Lemma lem5273759 : term75 = term76.
Proof. exact (TRANS (@lem5273660) (@lem5273706)). Qed.
Lemma lem5273760 : term76 = term75.
Proof. exact (SYM (@lem5273759)). Qed.
Lemma lem5273761 (s : real -> Prop) (b : real) (h1 : term36 s b) : term36 s b.
Proof. exact (h1). Qed.
Lemma lem5273763 (p : Prop) : p = (term61 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5273764 (s : real -> Prop) (b : real) (a : real) : ((term31 s a) = (term54 b a)) = (term77 s b a).
Proof. exact (@lem5273763 ((term31 s a) = (term54 b a))). Qed.
Lemma lem5273765 (s : real -> Prop) (b : real) (a : real) : (term77 s b a) = ((term31 s a) = (term54 b a)).
Proof. exact (SYM (@lem5273764 s b a)). Qed.
Lemma lem5273766 (s : real -> Prop) (b : real) (a : real) (h1 : term78 s b a) : term78 s b a.
Proof. exact (h1). Qed.
Lemma lem5273775 (s : real -> Prop) (c : real) (x : real) : (term79 s c x) = (term80 s c x).
Proof. exact (@lem17362 (s x) (real_le c x)). Qed.
Lemma lem5273780 (s : real -> Prop) (c : real) (x : real) : (term27 s c x) = (term81 s c x).
Proof. exact (@lem17265 (s x) (real_le c x)). Qed.
Lemma lem5273781 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5273782 (s : real -> Prop) (c : real) : (term84 s c) = (term85 s c).
Proof. exact (@lem5273781 (term29 s c)). Qed.
Lemma lem5273783 (s : real -> Prop) (c : real) (x : real) : (term86 s c x) = (term27 s c x).
Proof. exact (eq_refl (term86 s c x)). Qed.
Lemma lem5273784 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5273785 (s : real -> Prop) (c : real) (x : real) : (term87 s c x) = (term79 s c x).
Proof. exact (MK_COMB (@lem5273784) (@lem5273783 s c x)). Qed.
Lemma lem5273786 (s : real -> Prop) (c : real) (x : real) : (term87 s c x) = (term80 s c x).
Proof. exact (TRANS (@lem5273785 s c x) (@lem5273775 s c x)). Qed.
Lemma lem5273787 (s : real -> Prop) (c : real) : (term88 s c) = (term89 s c).
Proof. exact (fun_ext (fun x : real => @lem5273786 s c x)). Qed.
Lemma lem5273788 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5273789 (s : real -> Prop) (c : real) : (term85 s c) = (term90 s c).
Proof. exact (MK_COMB (@lem5273788) (@lem5273787 s c)). Qed.
Lemma lem5273790 (s : real -> Prop) (c : real) : (term84 s c) = (term90 s c).
Proof. exact (TRANS (@lem5273782 s c) (@lem5273789 s c)). Qed.
Lemma lem5273791 (s : real -> Prop) (c : real) : (term29 s c) = (term91 s c).
Proof. exact (fun_ext (fun x : real => @lem5273780 s c x)). Qed.
Lemma lem5273792 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273793 (s : real -> Prop) (c : real) : (term31 s c) = (term92 s c).
Proof. exact (MK_COMB (@lem5273792) (@lem5273791 s c)). Qed.
Lemma lem5273794 (c : real) (b : real) : (term93 c b) = (term93 c b).
Proof. exact (eq_refl (term93 c b)). Qed.
Lemma lem5273795 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5273796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5273797 (s : real -> Prop) (c : real) : (term94 s c) = (term95 s c).
Proof. exact (MK_COMB (@lem5273796) (@lem5273790 s c)). Qed.
Lemma lem5273798 (s : real -> Prop) (c : real) (b : real) : (term96 s c b) = (term97 s c b).
Proof. exact (MK_COMB (@lem5273797 s c) (@lem5273795 c b)). Qed.
Lemma lem5273799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5273800 (s : real -> Prop) (c : real) : (term98 s c) = (term99 s c).
Proof. exact (MK_COMB (@lem5273799) (@lem5273793 s c)). Qed.
Lemma lem5273801 (s : real -> Prop) (c : real) (b : real) : (term100 s c b) = (term101 s c b).
Proof. exact (MK_COMB (@lem5273800 s c) (@lem5273794 c b)). Qed.
Lemma lem5273802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5273803 (s : real -> Prop) (c : real) (b : real) : (term102 s c b) = (term103 s c b).
Proof. exact (MK_COMB (@lem5273802) (@lem5273801 s c b)). Qed.
Lemma lem5273804 (s : real -> Prop) (c : real) (b : real) : (term104 s c b) = (term105 s c b).
Proof. exact (MK_COMB (@lem5273803 s c b) (@lem5273798 s c b)). Qed.
Lemma lem5273805 (s : real -> Prop) (c : real) (b : real) : ((term31 s c) = (real_le c b)) = (term104 s c b).
Proof. exact (@lem17784 (term31 s c) (real_le c b)). Qed.
Lemma lem5273806 (s : real -> Prop) (c : real) (b : real) : ((term31 s c) = (real_le c b)) = (term105 s c b).
Proof. exact (TRANS (@lem5273805 s c b) (@lem5273804 s c b)). Qed.
Lemma lem5273807 (s : real -> Prop) (b : real) : (term35 s b) = (term106 s b).
Proof. exact (fun_ext (fun c : real => @lem5273806 s c b)). Qed.
Lemma lem5273808 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273809 (s : real -> Prop) (b : real) : (term36 s b) = (term107 s b).
Proof. exact (MK_COMB (@lem5273808) (@lem5273807 s b)). Qed.
Lemma lem5273811 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5273812 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem5273811 real P Q). Qed.
Lemma lem5273813 (s : real -> Prop) (b : real) : (term112 s b) = (term113 s b).
Proof. exact (@lem5273812 (term114 s b) (term115 s b)). Qed.
Lemma lem5273814 (s : real -> Prop) (c : real) (b : real) : (term116 s b c) = (term101 s c b).
Proof. exact (eq_refl (term116 s b c)). Qed.
Lemma lem5273815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5273816 (s : real -> Prop) (c : real) (b : real) : (term117 s b c) = (term103 s c b).
Proof. exact (MK_COMB (@lem5273815) (@lem5273814 s c b)). Qed.
Lemma lem5273817 (s : real -> Prop) (c : real) (b : real) : (term118 s b c) = (term97 s c b).
Proof. exact (eq_refl (term118 s b c)). Qed.
Lemma lem5273818 (s : real -> Prop) (c : real) (b : real) : (term119 s b c) = (term105 s c b).
Proof. exact (MK_COMB (@lem5273816 s c b) (@lem5273817 s c b)). Qed.
Lemma lem5273819 (s : real -> Prop) (b : real) : (term120 s b) = (term106 s b).
Proof. exact (fun_ext (fun c : real => @lem5273818 s c b)). Qed.
Lemma lem5273820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273821 (s : real -> Prop) (b : real) : (term112 s b) = (term107 s b).
Proof. exact (MK_COMB (@lem5273820) (@lem5273819 s b)). Qed.
Lemma lem5273822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5273823 (s : real -> Prop) (b : real) : (term121 s b) = (term122 s b).
Proof. exact (MK_COMB (@lem5273822) (@lem5273821 s b)). Qed.
Lemma lem5273824 (s : real -> Prop) (c : real) (b : real) : (term116 s b c) = (term101 s c b).
Proof. exact (eq_refl (term116 s b c)). Qed.
Lemma lem5273825 (s : real -> Prop) (b : real) : (term123 s b) = (term114 s b).
Proof. exact (fun_ext (fun c : real => @lem5273824 s c b)). Qed.
Lemma lem5273826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273827 (s : real -> Prop) (b : real) : (term124 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5273826) (@lem5273825 s b)). Qed.
Lemma lem5273828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5273829 (s : real -> Prop) (b : real) : (term126 s b) = (term127 s b).
Proof. exact (MK_COMB (@lem5273828) (@lem5273827 s b)). Qed.
Lemma lem5273830 (s : real -> Prop) (c : real) (b : real) : (term118 s b c) = (term97 s c b).
Proof. exact (eq_refl (term118 s b c)). Qed.
Lemma lem5273831 (s : real -> Prop) (b : real) : (term128 s b) = (term115 s b).
Proof. exact (fun_ext (fun c : real => @lem5273830 s c b)). Qed.
Lemma lem5273832 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5273833 (s : real -> Prop) (b : real) : (term129 s b) = (term130 s b).
Proof. exact (MK_COMB (@lem5273832) (@lem5273831 s b)). Qed.
Lemma lem5273834 (s : real -> Prop) (b : real) : (term113 s b) = (term131 s b).
Proof. exact (MK_COMB (@lem5273829 s b) (@lem5273833 s b)). Qed.
Lemma lem5273835 (s : real -> Prop) (b : real) : ((term112 s b) = (term113 s b)) = ((term107 s b) = (term131 s b)).
Proof. exact (MK_COMB (@lem5273823 s b) (@lem5273834 s b)). Qed.
Lemma lem5273836 (s : real -> Prop) (b : real) : (term107 s b) = (term131 s b).
Proof. exact (EQ_MP (@lem5273835 s b) (@lem5273813 s b)). Qed.
Lemma lem5274010 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5274011 (P : real -> Prop) (Q : Prop) : (term134 P Q) = (term135 P Q).
Proof. exact (@lem5274010 real P Q). Qed.
Lemma lem5274012 (s : real -> Prop) (c : real) (b : real) : (term136 s c b) = (term137 s c b).
Proof. exact (@lem5274011 (term89 s c) (real_le c b)). Qed.
Lemma lem5274013 (s : real -> Prop) (c : real) (x : real) : (term138 s c x) = (term80 s c x).
Proof. exact (eq_refl (term138 s c x)). Qed.
Lemma lem5274014 (s : real -> Prop) (c : real) : (term139 s c) = (term89 s c).
Proof. exact (fun_ext (fun x : real => @lem5274013 s c x)). Qed.
Lemma lem5274015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274016 (s : real -> Prop) (c : real) : (term140 s c) = (term90 s c).
Proof. exact (MK_COMB (@lem5274015) (@lem5274014 s c)). Qed.
Lemma lem5274017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274018 (s : real -> Prop) (c : real) : (term141 s c) = (term95 s c).
Proof. exact (MK_COMB (@lem5274017) (@lem5274016 s c)). Qed.
Lemma lem5274019 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5274020 (s : real -> Prop) (c : real) (b : real) : (term136 s c b) = (term97 s c b).
Proof. exact (MK_COMB (@lem5274018 s c) (@lem5274019 c b)). Qed.
Lemma lem5274021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274022 (s : real -> Prop) (c : real) (b : real) : (term142 s c b) = (term143 s c b).
Proof. exact (MK_COMB (@lem5274021) (@lem5274020 s c b)). Qed.
Lemma lem5274023 (s : real -> Prop) (c : real) (x : real) : (term138 s c x) = (term80 s c x).
Proof. exact (eq_refl (term138 s c x)). Qed.
Lemma lem5274024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274025 (s : real -> Prop) (c : real) (x : real) : (term144 s c x) = (term145 s c x).
Proof. exact (MK_COMB (@lem5274024) (@lem5274023 s c x)). Qed.
Lemma lem5274026 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5274027 (s : real -> Prop) (x : real) (c : real) (b : real) : (term146 s x c b) = (term147 s x c b).
Proof. exact (MK_COMB (@lem5274025 s c x) (@lem5274026 c b)). Qed.
Lemma lem5274028 (s : real -> Prop) (c : real) (b : real) : (term148 s c b) = (term149 s c b).
Proof. exact (fun_ext (fun x : real => @lem5274027 s x c b)). Qed.
Lemma lem5274029 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274030 (s : real -> Prop) (c : real) (b : real) : (term137 s c b) = (term150 s c b).
Proof. exact (MK_COMB (@lem5274029) (@lem5274028 s c b)). Qed.
Lemma lem5274031 (s : real -> Prop) (c : real) (b : real) : ((term136 s c b) = (term137 s c b)) = ((term97 s c b) = (term150 s c b)).
Proof. exact (MK_COMB (@lem5274022 s c b) (@lem5274030 s c b)). Qed.
Lemma lem5274032 (s : real -> Prop) (c : real) (b : real) : (term97 s c b) = (term150 s c b).
Proof. exact (EQ_MP (@lem5274031 s c b) (@lem5274012 s c b)). Qed.
Lemma lem5274033 (s : real -> Prop) (b : real) : (term115 s b) = (term151 s b).
Proof. exact (fun_ext (fun c : real => @lem5274032 s c b)). Qed.
Lemma lem5274034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274035 (s : real -> Prop) (b : real) : (term130 s b) = (term152 s b).
Proof. exact (MK_COMB (@lem5274034) (@lem5274033 s b)). Qed.
Lemma lem5274037 {A B : Type'} (P : type1413 A B) : (term153 A B P) = (term154 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5274038 (P : type1626) : (term155 P) = (term156 P).
Proof. exact (@lem5274037 real real P). Qed.
Lemma lem5274039 (s : real -> Prop) (b : real) : (term157 s b) = (term158 s b).
Proof. exact (@lem5274038 (term159 s b)). Qed.
Lemma lem5274040 (s : real -> Prop) (c : real) (b : real) : (term160 s b c) = (term149 s c b).
Proof. exact (eq_refl (term160 s b c)). Qed.
Lemma lem5274041 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5274042 (s : real -> Prop) (c : real) (b : real) (x : real) : (term161 s b c x) = (term162 s c b x).
Proof. exact (MK_COMB (@lem5274040 s c b) (@lem5274041 x)). Qed.
Lemma lem5274043 (s : real -> Prop) (x : real) (c : real) (b : real) : (term162 s c b x) = (term147 s x c b).
Proof. exact (eq_refl (term162 s c b x)). Qed.
Lemma lem5274044 (s : real -> Prop) (x : real) (c : real) (b : real) : (term161 s b c x) = (term147 s x c b).
Proof. exact (TRANS (@lem5274042 s c b x) (@lem5274043 s x c b)). Qed.
Lemma lem5274045 (s : real -> Prop) (c : real) (b : real) : (term163 s b c) = (term149 s c b).
Proof. exact (fun_ext (fun x : real => @lem5274044 s x c b)). Qed.
Lemma lem5274046 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274047 (s : real -> Prop) (c : real) (b : real) : (term164 s b c) = (term150 s c b).
Proof. exact (MK_COMB (@lem5274046) (@lem5274045 s c b)). Qed.
Lemma lem5274048 (s : real -> Prop) (b : real) : (term165 s b) = (term151 s b).
Proof. exact (fun_ext (fun c : real => @lem5274047 s c b)). Qed.
Lemma lem5274049 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274050 (s : real -> Prop) (b : real) : (term157 s b) = (term152 s b).
Proof. exact (MK_COMB (@lem5274049) (@lem5274048 s b)). Qed.
Lemma lem5274051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274052 (s : real -> Prop) (b : real) : (term166 s b) = (term167 s b).
Proof. exact (MK_COMB (@lem5274051) (@lem5274050 s b)). Qed.
Lemma lem5274053 (s : real -> Prop) (c : real) (b : real) : (term160 s b c) = (term149 s c b).
Proof. exact (eq_refl (term160 s b c)). Qed.
Lemma lem5274054 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5274055 (s : real -> Prop) (b : real) (x : real -> real) (c : real) : (term168 s b x c) = (term169 s b x c).
Proof. exact (MK_COMB (@lem5274053 s c b) (@lem5274054 x c)). Qed.
Lemma lem5274056 (s : real -> Prop) (x : real -> real) (c : real) (b : real) : (term169 s b x c) = (term170 s x c b).
Proof. exact (eq_refl (term169 s b x c)). Qed.
Lemma lem5274057 (s : real -> Prop) (x : real -> real) (c : real) (b : real) : (term168 s b x c) = (term170 s x c b).
Proof. exact (TRANS (@lem5274055 s b x c) (@lem5274056 s x c b)). Qed.
Lemma lem5274058 (s : real -> Prop) (x : real -> real) (b : real) : (term171 s b x) = (term172 s x b).
Proof. exact (fun_ext (fun c : real => @lem5274057 s x c b)). Qed.
Lemma lem5274059 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274060 (s : real -> Prop) (x : real -> real) (b : real) : (term173 s b x) = (term174 s x b).
Proof. exact (MK_COMB (@lem5274059) (@lem5274058 s x b)). Qed.
Lemma lem5274061 (s : real -> Prop) (b : real) : (term175 s b) = (term176 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5274060 s x b)). Qed.
Lemma lem5274062 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5274063 (s : real -> Prop) (b : real) : (term158 s b) = (term177 s b).
Proof. exact (MK_COMB (@lem5274062) (@lem5274061 s b)). Qed.
Lemma lem5274064 (s : real -> Prop) (b : real) : ((term157 s b) = (term158 s b)) = ((term152 s b) = (term177 s b)).
Proof. exact (MK_COMB (@lem5274052 s b) (@lem5274063 s b)). Qed.
Lemma lem5274065 (s : real -> Prop) (b : real) : (term152 s b) = (term177 s b).
Proof. exact (EQ_MP (@lem5274064 s b) (@lem5274039 s b)). Qed.
Lemma lem5274066 (s : real -> Prop) (b : real) : (term130 s b) = (term177 s b).
Proof. exact (TRANS (@lem5274035 s b) (@lem5274065 s b)). Qed.
Lemma lem5274067 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (eq_refl (term127 s b)). Qed.
Lemma lem5274068 (s : real -> Prop) (b : real) : (term131 s b) = (term178 s b).
Proof. exact (MK_COMB (@lem5274067 s b) (@lem5274066 s b)). Qed.
Lemma lem5274070 {A : Type'} (P : Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5274071 (P : Prop) (Q : type1028) : (term181 P Q) = (term182 P Q).
Proof. exact (@lem5274070 (real -> real) P Q). Qed.
Lemma lem5274072 (s : real -> Prop) (b : real) : (term183 s b) = (term184 s b).
Proof. exact (@lem5274071 (term125 s b) (term176 s b)). Qed.
Lemma lem5274073 (s : real -> Prop) (x : real -> real) (b : real) : (term185 s b x) = (term174 s x b).
Proof. exact (eq_refl (term185 s b x)). Qed.
Lemma lem5274074 (s : real -> Prop) (b : real) : (term186 s b) = (term176 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5274073 s x b)). Qed.
Lemma lem5274075 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5274076 (s : real -> Prop) (b : real) : (term187 s b) = (term177 s b).
Proof. exact (MK_COMB (@lem5274075) (@lem5274074 s b)). Qed.
Lemma lem5274077 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (eq_refl (term127 s b)). Qed.
Lemma lem5274078 (s : real -> Prop) (b : real) : (term183 s b) = (term178 s b).
Proof. exact (MK_COMB (@lem5274077 s b) (@lem5274076 s b)). Qed.
Lemma lem5274079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274080 (s : real -> Prop) (b : real) : (term188 s b) = (term189 s b).
Proof. exact (MK_COMB (@lem5274079) (@lem5274078 s b)). Qed.
Lemma lem5274081 (s : real -> Prop) (x : real -> real) (b : real) : (term185 s b x) = (term174 s x b).
Proof. exact (eq_refl (term185 s b x)). Qed.
Lemma lem5274082 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (eq_refl (term127 s b)). Qed.
Lemma lem5274083 (s : real -> Prop) (x : real -> real) (b : real) : (term190 s b x) = (term191 s x b).
Proof. exact (MK_COMB (@lem5274082 s b) (@lem5274081 s x b)). Qed.
Lemma lem5274084 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5274083 s x b)). Qed.
Lemma lem5274085 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5274086 (s : real -> Prop) (b : real) : (term184 s b) = (term194 s b).
Proof. exact (MK_COMB (@lem5274085) (@lem5274084 s b)). Qed.
Lemma lem5274087 (s : real -> Prop) (b : real) : ((term183 s b) = (term184 s b)) = ((term178 s b) = (term194 s b)).
Proof. exact (MK_COMB (@lem5274080 s b) (@lem5274086 s b)). Qed.
Lemma lem5274088 (s : real -> Prop) (b : real) : (term178 s b) = (term194 s b).
Proof. exact (EQ_MP (@lem5274087 s b) (@lem5274072 s b)). Qed.
Lemma lem5274089 (s : real -> Prop) (b : real) : (term131 s b) = (term194 s b).
Proof. exact (TRANS (@lem5274068 s b) (@lem5274088 s b)). Qed.
Lemma lem5274090 (s : real -> Prop) (b : real) : (term107 s b) = (term194 s b).
Proof. exact (TRANS (@lem5273836 s b) (@lem5274089 s b)). Qed.
Lemma lem5274091 (s : real -> Prop) (b : real) : (term36 s b) = (term194 s b).
Proof. exact (TRANS (@lem5273809 s b) (@lem5274090 s b)). Qed.
Lemma lem5274092 (s : real -> Prop) (b : real) (h1 : term36 s b) : term194 s b.
Proof. exact (EQ_MP (@lem5274091 s b) (@lem5273761 s b h1)). Qed.
Lemma lem5274101 (s : real -> Prop) (a : real) (x : real) : (term79 s a x) = (term80 s a x).
Proof. exact (@lem17362 (s x) (real_le a x)). Qed.
Lemma lem5274106 (s : real -> Prop) (a : real) (x : real) : (term27 s a x) = (term81 s a x).
Proof. exact (@lem17265 (s x) (real_le a x)). Qed.
Lemma lem5274107 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5274108 (s : real -> Prop) (a : real) : (term84 s a) = (term85 s a).
Proof. exact (@lem5274107 (term29 s a)). Qed.
Lemma lem5274109 (s : real -> Prop) (a : real) (x : real) : (term86 s a x) = (term27 s a x).
Proof. exact (eq_refl (term86 s a x)). Qed.
Lemma lem5274110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5274111 (s : real -> Prop) (a : real) (x : real) : (term87 s a x) = (term79 s a x).
Proof. exact (MK_COMB (@lem5274110) (@lem5274109 s a x)). Qed.
Lemma lem5274112 (s : real -> Prop) (a : real) (x : real) : (term87 s a x) = (term80 s a x).
Proof. exact (TRANS (@lem5274111 s a x) (@lem5274101 s a x)). Qed.
Lemma lem5274113 (s : real -> Prop) (a : real) : (term88 s a) = (term89 s a).
Proof. exact (fun_ext (fun x : real => @lem5274112 s a x)). Qed.
Lemma lem5274114 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274115 (s : real -> Prop) (a : real) : (term85 s a) = (term90 s a).
Proof. exact (MK_COMB (@lem5274114) (@lem5274113 s a)). Qed.
Lemma lem5274116 (s : real -> Prop) (a : real) : (term84 s a) = (term90 s a).
Proof. exact (TRANS (@lem5274108 s a) (@lem5274115 s a)). Qed.
Lemma lem5274117 (s : real -> Prop) (a : real) : (term29 s a) = (term91 s a).
Proof. exact (fun_ext (fun x : real => @lem5274106 s a x)). Qed.
Lemma lem5274118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274119 (s : real -> Prop) (a : real) : (term31 s a) = (term92 s a).
Proof. exact (MK_COMB (@lem5274118) (@lem5274117 s a)). Qed.
Lemma lem5274128 (b : real) (a : real) (x : real) : (term195 b a x) = (term196 b a x).
Proof. exact (@lem17362 (x = b) (real_le a x)). Qed.
Lemma lem5274133 (b : real) (a : real) (x : real) : (term50 b a x) = (term197 b a x).
Proof. exact (@lem17265 (x = b) (real_le a x)). Qed.
Lemma lem5274134 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5274135 (b : real) (a : real) : (term198 b a) = (term199 b a).
Proof. exact (@lem5274134 (term52 b a)). Qed.
Lemma lem5274136 (b : real) (a : real) (x : real) : (term200 b a x) = (term50 b a x).
Proof. exact (eq_refl (term200 b a x)). Qed.
Lemma lem5274137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5274138 (b : real) (a : real) (x : real) : (term201 b a x) = (term195 b a x).
Proof. exact (MK_COMB (@lem5274137) (@lem5274136 b a x)). Qed.
Lemma lem5274139 (b : real) (a : real) (x : real) : (term201 b a x) = (term196 b a x).
Proof. exact (TRANS (@lem5274138 b a x) (@lem5274128 b a x)). Qed.
Lemma lem5274140 (b : real) (a : real) : (term202 b a) = (term203 b a).
Proof. exact (fun_ext (fun x : real => @lem5274139 b a x)). Qed.
Lemma lem5274141 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274142 (b : real) (a : real) : (term199 b a) = (term204 b a).
Proof. exact (MK_COMB (@lem5274141) (@lem5274140 b a)). Qed.
Lemma lem5274143 (b : real) (a : real) : (term198 b a) = (term204 b a).
Proof. exact (TRANS (@lem5274135 b a) (@lem5274142 b a)). Qed.
Lemma lem5274144 (b : real) (a : real) : (term52 b a) = (term205 b a).
Proof. exact (fun_ext (fun x : real => @lem5274133 b a x)). Qed.
Lemma lem5274145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274146 (b : real) (a : real) : (term54 b a) = (term206 b a).
Proof. exact (MK_COMB (@lem5274145) (@lem5274144 b a)). Qed.
Lemma lem5274147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5274148 (s : real -> Prop) (a : real) : (term207 s a) = (term208 s a).
Proof. exact (MK_COMB (@lem5274147) (@lem5274116 s a)). Qed.
Lemma lem5274149 (s : real -> Prop) (b : real) (a : real) : (term209 s b a) = (term210 s b a).
Proof. exact (MK_COMB (@lem5274148 s a) (@lem5274146 b a)). Qed.
Lemma lem5274150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5274151 (s : real -> Prop) (a : real) : (term211 s a) = (term212 s a).
Proof. exact (MK_COMB (@lem5274150) (@lem5274119 s a)). Qed.
Lemma lem5274152 (s : real -> Prop) (b : real) (a : real) : (term213 s b a) = (term214 s b a).
Proof. exact (MK_COMB (@lem5274151 s a) (@lem5274143 b a)). Qed.
Lemma lem5274153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274154 (s : real -> Prop) (b : real) (a : real) : (term215 s b a) = (term216 s b a).
Proof. exact (MK_COMB (@lem5274153) (@lem5274152 s b a)). Qed.
Lemma lem5274155 (s : real -> Prop) (b : real) (a : real) : (term217 s b a) = (term218 s b a).
Proof. exact (MK_COMB (@lem5274154 s b a) (@lem5274149 s b a)). Qed.
Lemma lem5274156 (s : real -> Prop) (b : real) (a : real) : (term78 s b a) = (term217 s b a).
Proof. exact (@lem17646 (term31 s a) (term54 b a)). Qed.
Lemma lem5274157 (s : real -> Prop) (b : real) (a : real) : (term78 s b a) = (term218 s b a).
Proof. exact (TRANS (@lem5274156 s b a) (@lem5274155 s b a)). Qed.
Lemma lem5274332 {A : Type'} (P : Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5274333 (P : Prop) (Q : real -> Prop) : (term219 P Q) = (term220 P Q).
Proof. exact (@lem5274332 real P Q). Qed.
Lemma lem5274334 (s : real -> Prop) (b : real) (a : real) : (term221 s b a) = (term222 s b a).
Proof. exact (@lem5274333 (term92 s a) (term203 b a)). Qed.
Lemma lem5274335 (b : real) (a : real) (x : real) : (term223 b a x) = (term196 b a x).
Proof. exact (eq_refl (term223 b a x)). Qed.
Lemma lem5274336 (b : real) (a : real) : (term224 b a) = (term203 b a).
Proof. exact (fun_ext (fun x : real => @lem5274335 b a x)). Qed.
Lemma lem5274337 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274338 (b : real) (a : real) : (term225 b a) = (term204 b a).
Proof. exact (MK_COMB (@lem5274337) (@lem5274336 b a)). Qed.
Lemma lem5274339 (s : real -> Prop) (a : real) : (term212 s a) = (term212 s a).
Proof. exact (eq_refl (term212 s a)). Qed.
Lemma lem5274340 (s : real -> Prop) (b : real) (a : real) : (term221 s b a) = (term214 s b a).
Proof. exact (MK_COMB (@lem5274339 s a) (@lem5274338 b a)). Qed.
Lemma lem5274341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274342 (s : real -> Prop) (b : real) (a : real) : (term226 s b a) = (term227 s b a).
Proof. exact (MK_COMB (@lem5274341) (@lem5274340 s b a)). Qed.
Lemma lem5274343 (b : real) (a : real) (x : real) : (term223 b a x) = (term196 b a x).
Proof. exact (eq_refl (term223 b a x)). Qed.
Lemma lem5274344 (s : real -> Prop) (a : real) : (term212 s a) = (term212 s a).
Proof. exact (eq_refl (term212 s a)). Qed.
Lemma lem5274345 (s : real -> Prop) (b : real) (a : real) (x : real) : (term228 s b a x) = (term229 s b a x).
Proof. exact (MK_COMB (@lem5274344 s a) (@lem5274343 b a x)). Qed.
Lemma lem5274346 (s : real -> Prop) (b : real) (a : real) : (term230 s b a) = (term231 s b a).
Proof. exact (fun_ext (fun x : real => @lem5274345 s b a x)). Qed.
Lemma lem5274347 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274348 (s : real -> Prop) (b : real) (a : real) : (term222 s b a) = (term232 s b a).
Proof. exact (MK_COMB (@lem5274347) (@lem5274346 s b a)). Qed.
Lemma lem5274349 (s : real -> Prop) (b : real) (a : real) : ((term221 s b a) = (term222 s b a)) = ((term214 s b a) = (term232 s b a)).
Proof. exact (MK_COMB (@lem5274342 s b a) (@lem5274348 s b a)). Qed.
Lemma lem5274350 (s : real -> Prop) (b : real) (a : real) : (term214 s b a) = (term232 s b a).
Proof. exact (EQ_MP (@lem5274349 s b a) (@lem5274334 s b a)). Qed.
Lemma lem5274351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274352 (s : real -> Prop) (b : real) (a : real) : (term216 s b a) = (term233 s b a).
Proof. exact (MK_COMB (@lem5274351) (@lem5274350 s b a)). Qed.
Lemma lem5274354 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5274355 (P : real -> Prop) (Q : Prop) : (term236 P Q) = (term237 P Q).
Proof. exact (@lem5274354 real P Q). Qed.
Lemma lem5274356 (s : real -> Prop) (b : real) (a : real) : (term238 s b a) = (term239 s b a).
Proof. exact (@lem5274355 (term89 s a) (term206 b a)). Qed.
Lemma lem5274357 (s : real -> Prop) (a : real) (x : real) : (term138 s a x) = (term80 s a x).
Proof. exact (eq_refl (term138 s a x)). Qed.
Lemma lem5274358 (s : real -> Prop) (a : real) : (term139 s a) = (term89 s a).
Proof. exact (fun_ext (fun x : real => @lem5274357 s a x)). Qed.
Lemma lem5274359 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274360 (s : real -> Prop) (a : real) : (term140 s a) = (term90 s a).
Proof. exact (MK_COMB (@lem5274359) (@lem5274358 s a)). Qed.
Lemma lem5274361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5274362 (s : real -> Prop) (a : real) : (term240 s a) = (term208 s a).
Proof. exact (MK_COMB (@lem5274361) (@lem5274360 s a)). Qed.
Lemma lem5274363 (b : real) (a : real) : (term206 b a) = (term206 b a).
Proof. exact (eq_refl (term206 b a)). Qed.
Lemma lem5274364 (s : real -> Prop) (b : real) (a : real) : (term238 s b a) = (term210 s b a).
Proof. exact (MK_COMB (@lem5274362 s a) (@lem5274363 b a)). Qed.
Lemma lem5274365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274366 (s : real -> Prop) (b : real) (a : real) : (term241 s b a) = (term242 s b a).
Proof. exact (MK_COMB (@lem5274365) (@lem5274364 s b a)). Qed.
Lemma lem5274367 (s : real -> Prop) (a : real) (x : real) : (term138 s a x) = (term80 s a x).
Proof. exact (eq_refl (term138 s a x)). Qed.
Lemma lem5274368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5274369 (s : real -> Prop) (a : real) (x : real) : (term243 s a x) = (term244 s a x).
Proof. exact (MK_COMB (@lem5274368) (@lem5274367 s a x)). Qed.
Lemma lem5274370 (b : real) (a : real) : (term206 b a) = (term206 b a).
Proof. exact (eq_refl (term206 b a)). Qed.
Lemma lem5274371 (s : real -> Prop) (x : real) (b : real) (a : real) : (term245 s x b a) = (term246 s x b a).
Proof. exact (MK_COMB (@lem5274369 s a x) (@lem5274370 b a)). Qed.
Lemma lem5274372 (s : real -> Prop) (b : real) (a : real) : (term247 s b a) = (term248 s b a).
Proof. exact (fun_ext (fun x : real => @lem5274371 s x b a)). Qed.
Lemma lem5274373 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274374 (s : real -> Prop) (b : real) (a : real) : (term239 s b a) = (term249 s b a).
Proof. exact (MK_COMB (@lem5274373) (@lem5274372 s b a)). Qed.
Lemma lem5274375 (s : real -> Prop) (b : real) (a : real) : ((term238 s b a) = (term239 s b a)) = ((term210 s b a) = (term249 s b a)).
Proof. exact (MK_COMB (@lem5274366 s b a) (@lem5274374 s b a)). Qed.
Lemma lem5274376 (s : real -> Prop) (b : real) (a : real) : (term210 s b a) = (term249 s b a).
Proof. exact (EQ_MP (@lem5274375 s b a) (@lem5274356 s b a)). Qed.
Lemma lem5274377 (s : real -> Prop) (b : real) (a : real) : (term218 s b a) = (term250 s b a).
Proof. exact (MK_COMB (@lem5274352 s b a) (@lem5274376 s b a)). Qed.
Lemma lem5274379 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term251 A P Q) = (term252 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5274380 (P : real -> Prop) (Q : real -> Prop) : (term253 P Q) = (term254 P Q).
Proof. exact (@lem5274379 real P Q). Qed.
Lemma lem5274381 (s : real -> Prop) (b : real) (a : real) : (term255 s b a) = (term256 s b a).
Proof. exact (@lem5274380 (term231 s b a) (term248 s b a)). Qed.
Lemma lem5274382 (s : real -> Prop) (b : real) (a : real) (x : real) : (term257 s b a x) = (term229 s b a x).
Proof. exact (eq_refl (term257 s b a x)). Qed.
Lemma lem5274383 (s : real -> Prop) (b : real) (a : real) : (term258 s b a) = (term231 s b a).
Proof. exact (fun_ext (fun x : real => @lem5274382 s b a x)). Qed.
Lemma lem5274384 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274385 (s : real -> Prop) (b : real) (a : real) : (term259 s b a) = (term232 s b a).
Proof. exact (MK_COMB (@lem5274384) (@lem5274383 s b a)). Qed.
Lemma lem5274386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274387 (s : real -> Prop) (b : real) (a : real) : (term260 s b a) = (term233 s b a).
Proof. exact (MK_COMB (@lem5274386) (@lem5274385 s b a)). Qed.
Lemma lem5274388 (s : real -> Prop) (x : real) (b : real) (a : real) : (term261 s b a x) = (term246 s x b a).
Proof. exact (eq_refl (term261 s b a x)). Qed.
Lemma lem5274389 (s : real -> Prop) (b : real) (a : real) : (term262 s b a) = (term248 s b a).
Proof. exact (fun_ext (fun x : real => @lem5274388 s x b a)). Qed.
Lemma lem5274390 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274391 (s : real -> Prop) (b : real) (a : real) : (term263 s b a) = (term249 s b a).
Proof. exact (MK_COMB (@lem5274390) (@lem5274389 s b a)). Qed.
Lemma lem5274392 (s : real -> Prop) (b : real) (a : real) : (term255 s b a) = (term250 s b a).
Proof. exact (MK_COMB (@lem5274387 s b a) (@lem5274391 s b a)). Qed.
Lemma lem5274393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274394 (s : real -> Prop) (b : real) (a : real) : (term264 s b a) = (term265 s b a).
Proof. exact (MK_COMB (@lem5274393) (@lem5274392 s b a)). Qed.
Lemma lem5274395 (s : real -> Prop) (b : real) (a : real) (x : real) : (term257 s b a x) = (term229 s b a x).
Proof. exact (eq_refl (term257 s b a x)). Qed.
Lemma lem5274396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274397 (s : real -> Prop) (b : real) (a : real) (x : real) : (term266 s b a x) = (term267 s b a x).
Proof. exact (MK_COMB (@lem5274396) (@lem5274395 s b a x)). Qed.
Lemma lem5274398 (s : real -> Prop) (x : real) (b : real) (a : real) : (term261 s b a x) = (term246 s x b a).
Proof. exact (eq_refl (term261 s b a x)). Qed.
Lemma lem5274399 (s : real -> Prop) (x : real) (b : real) (a : real) : (term268 s b a x) = (term269 s x b a).
Proof. exact (MK_COMB (@lem5274397 s b a x) (@lem5274398 s x b a)). Qed.
Lemma lem5274400 (s : real -> Prop) (b : real) (a : real) : (term270 s b a) = (term271 s b a).
Proof. exact (fun_ext (fun x : real => @lem5274399 s x b a)). Qed.
Lemma lem5274401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5274402 (s : real -> Prop) (b : real) (a : real) : (term256 s b a) = (term272 s b a).
Proof. exact (MK_COMB (@lem5274401) (@lem5274400 s b a)). Qed.
Lemma lem5274403 (s : real -> Prop) (b : real) (a : real) : ((term255 s b a) = (term256 s b a)) = ((term250 s b a) = (term272 s b a)).
Proof. exact (MK_COMB (@lem5274394 s b a) (@lem5274402 s b a)). Qed.
Lemma lem5274404 (s : real -> Prop) (b : real) (a : real) : (term250 s b a) = (term272 s b a).
Proof. exact (EQ_MP (@lem5274403 s b a) (@lem5274381 s b a)). Qed.
Lemma lem5274406 (s : real -> Prop) (b : real) (a : real) : (term218 s b a) = (term272 s b a).
Proof. exact (TRANS (@lem5274377 s b a) (@lem5274404 s b a)). Qed.
Lemma lem5274407 (s : real -> Prop) (b : real) (a : real) : (term78 s b a) = (term272 s b a).
Proof. exact (TRANS (@lem5274157 s b a) (@lem5274406 s b a)). Qed.
Lemma lem5274408 (s : real -> Prop) (b : real) (a : real) (h1 : term78 s b a) : term272 s b a.
Proof. exact (EQ_MP (@lem5274407 s b a) (@lem5273766 s b a h1)). Qed.
Lemma lem5274409 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term269 s x b a) : term269 s x b a.
Proof. exact (h1). Qed.
Lemma lem5274410 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term191 s x' b.
Proof. exact (h1). Qed.
Lemma lem5274425 (b : real) (a : real) (x : real) : (term197 b a x) = (term197 b a x).
Proof. exact (eq_refl (term197 b a x)). Qed.
Lemma lem5274426 (b : real) (a : real) : (term205 b a) = (term205 b a).
Proof. exact (fun_ext (fun x : real => @lem5274425 b a x)). Qed.
Lemma lem5274427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274428 (b : real) (a : real) : (term206 b a) = (term206 b a).
Proof. exact (MK_COMB (@lem5274427) (@lem5274426 b a)). Qed.
Lemma lem5274443 (s : real -> Prop) (a : real) (x : real) : (term244 s a x) = (term244 s a x).
Proof. exact (eq_refl (term244 s a x)). Qed.
Lemma lem5274444 (s : real -> Prop) (x : real) (b : real) (a : real) : (term246 s x b a) = (term246 s x b a).
Proof. exact (MK_COMB (@lem5274443 s a x) (@lem5274428 b a)). Qed.
Lemma lem5274459 (b : real) (a : real) (x : real) : (term196 b a x) = (term196 b a x).
Proof. exact (eq_refl (term196 b a x)). Qed.
Lemma lem5274472 (s : real -> Prop) (a : real) (x : real) : (term81 s a x) = (term81 s a x).
Proof. exact (eq_refl (term81 s a x)). Qed.
Lemma lem5274473 (s : real -> Prop) (a : real) : (term91 s a) = (term91 s a).
Proof. exact (fun_ext (fun x : real => @lem5274472 s a x)). Qed.
Lemma lem5274474 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274475 (s : real -> Prop) (a : real) : (term92 s a) = (term92 s a).
Proof. exact (MK_COMB (@lem5274474) (@lem5274473 s a)). Qed.
Lemma lem5274476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5274477 (s : real -> Prop) (a : real) : (term212 s a) = (term212 s a).
Proof. exact (MK_COMB (@lem5274476) (@lem5274475 s a)). Qed.
Lemma lem5274478 (s : real -> Prop) (b : real) (a : real) (x : real) : (term229 s b a x) = (term229 s b a x).
Proof. exact (MK_COMB (@lem5274477 s a) (@lem5274459 b a x)). Qed.
Lemma lem5274479 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274480 (s : real -> Prop) (b : real) (a : real) (x : real) : (term267 s b a x) = (term267 s b a x).
Proof. exact (MK_COMB (@lem5274479) (@lem5274478 s b a x)). Qed.
Lemma lem5274481 (s : real -> Prop) (x : real) (b : real) (a : real) : (term269 s x b a) = (term269 s x b a).
Proof. exact (MK_COMB (@lem5274480 s b a x) (@lem5274444 s x b a)). Qed.
Lemma lem5274482 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term269 s x b a) : term269 s x b a.
Proof. exact (EQ_MP (@lem5274481 s x b a) (@lem5274409 s x b a h1)). Qed.
Lemma lem5274507 (s : real -> Prop) (x' : real -> real) (c : real) (b : real) : (term170 s x' c b) = (term170 s x' c b).
Proof. exact (eq_refl (term170 s x' c b)). Qed.
Lemma lem5274508 (s : real -> Prop) (x' : real -> real) (b : real) : (term172 s x' b) = (term172 s x' b).
Proof. exact (fun_ext (fun c : real => @lem5274507 s x' c b)). Qed.
Lemma lem5274509 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274510 (s : real -> Prop) (x' : real -> real) (b : real) : (term174 s x' b) = (term174 s x' b).
Proof. exact (MK_COMB (@lem5274509) (@lem5274508 s x' b)). Qed.
Lemma lem5274517 (c : real) (b : real) : (term93 c b) = (term93 c b).
Proof. exact (eq_refl (term93 c b)). Qed.
Lemma lem5274530 (s : real -> Prop) (c : real) (x : real) : (term81 s c x) = (term81 s c x).
Proof. exact (eq_refl (term81 s c x)). Qed.
Lemma lem5274531 (s : real -> Prop) (c : real) : (term91 s c) = (term91 s c).
Proof. exact (fun_ext (fun x : real => @lem5274530 s c x)). Qed.
Lemma lem5274532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274533 (s : real -> Prop) (c : real) : (term92 s c) = (term92 s c).
Proof. exact (MK_COMB (@lem5274532) (@lem5274531 s c)). Qed.
Lemma lem5274534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274535 (s : real -> Prop) (c : real) : (term99 s c) = (term99 s c).
Proof. exact (MK_COMB (@lem5274534) (@lem5274533 s c)). Qed.
Lemma lem5274536 (s : real -> Prop) (c : real) (b : real) : (term101 s c b) = (term101 s c b).
Proof. exact (MK_COMB (@lem5274535 s c) (@lem5274517 c b)). Qed.
Lemma lem5274537 (s : real -> Prop) (b : real) : (term114 s b) = (term114 s b).
Proof. exact (fun_ext (fun c : real => @lem5274536 s c b)). Qed.
Lemma lem5274538 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274539 (s : real -> Prop) (b : real) : (term125 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5274538) (@lem5274537 s b)). Qed.
Lemma lem5274540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5274541 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (MK_COMB (@lem5274540) (@lem5274539 s b)). Qed.
Lemma lem5274542 (s : real -> Prop) (x' : real -> real) (b : real) : (term191 s x' b) = (term191 s x' b).
Proof. exact (MK_COMB (@lem5274541 s b) (@lem5274510 s x' b)). Qed.
Lemma lem5274543 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term191 s x' b.
Proof. exact (EQ_MP (@lem5274542 s x' b) (@lem5274410 s x' b h1)). Qed.
Lemma lem5274544 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term174 s x' b.
Proof. exact (proj2 (@lem5274543 s x' b h1)). Qed.
Lemma lem5274545 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term125 s b.
Proof. exact (proj1 (@lem5274543 s x' b h1)). Qed.
Lemma lem5274546 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term229 s b a x.
Proof. exact (h1). Qed.
Lemma lem5274547 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term246 s x b a.
Proof. exact (h1). Qed.
Lemma lem5274548 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term196 b a x.
Proof. exact (proj2 (@lem5274546 s b a x h1)). Qed.
Lemma lem5274549 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term92 s a.
Proof. exact (proj1 (@lem5274546 s b a x h1)). Qed.
Lemma lem5274552 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term206 b a.
Proof. exact (proj2 (@lem5274547 s x b a h1)). Qed.
Lemma lem5274553 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term80 s a x.
Proof. exact (proj1 (@lem5274547 s x b a h1)). Qed.
Lemma lem5274621 (s : real -> Prop) (x' : real -> real) (c : real) (b : real) : (term170 s x' c b) = (term273 s x' c b).
Proof. exact (@lem19699 (term274 s x' c) (term275 x' c) (real_le c b)). Qed.
Lemma lem5274622 (s : real -> Prop) (x' : real -> real) (b : real) : (term172 s x' b) = (term276 s x' b).
Proof. exact (fun_ext (fun c : real => @lem5274621 s x' c b)). Qed.
Lemma lem5274623 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274625 (s : real -> Prop) (x' : real -> real) (b : real) : (term174 s x' b) = (term277 s x' b).
Proof. exact (MK_COMB (@lem5274623) (@lem5274622 s x' b)). Qed.
Lemma lem5274626 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term277 s x' b.
Proof. exact (EQ_MP (@lem5274625 s x' b) (@lem5274544 s x' b h1)). Qed.
Lemma lem5274634 (s : real -> Prop) (a : real) (x : real) : (term81 s a x) = (term81 s a x).
Proof. exact (eq_refl (term81 s a x)). Qed.
Lemma lem5274635 (s : real -> Prop) (a : real) : (term91 s a) = (term91 s a).
Proof. exact (fun_ext (fun x : real => @lem5274634 s a x)). Qed.
Lemma lem5274636 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274638 (s : real -> Prop) (a : real) : (term92 s a) = (term92 s a).
Proof. exact (MK_COMB (@lem5274636) (@lem5274635 s a)). Qed.
Lemma lem5274639 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term92 s a.
Proof. exact (EQ_MP (@lem5274638 s a) (@lem5274549 s b a x h1)). Qed.
Lemma lem5274649 {A : Type'} (P : A -> Prop) (Q : Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5274650 (P : real -> Prop) (Q : Prop) : (term280 P Q) = (term281 P Q).
Proof. exact (@lem5274649 real P Q). Qed.
Lemma lem5274651 (s : real -> Prop) (c : real) (b : real) : (term282 s c b) = (term283 s c b).
Proof. exact (@lem5274650 (term91 s c) (term93 c b)). Qed.
Lemma lem5274652 (s : real -> Prop) (c : real) (x : real) : (term284 s c x) = (term81 s c x).
Proof. exact (eq_refl (term284 s c x)). Qed.
Lemma lem5274653 (s : real -> Prop) (c : real) : (term285 s c) = (term91 s c).
Proof. exact (fun_ext (fun x : real => @lem5274652 s c x)). Qed.
Lemma lem5274654 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274655 (s : real -> Prop) (c : real) : (term286 s c) = (term92 s c).
Proof. exact (MK_COMB (@lem5274654) (@lem5274653 s c)). Qed.
Lemma lem5274656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274657 (s : real -> Prop) (c : real) : (term287 s c) = (term99 s c).
Proof. exact (MK_COMB (@lem5274656) (@lem5274655 s c)). Qed.
Lemma lem5274658 (c : real) (b : real) : (term93 c b) = (term93 c b).
Proof. exact (eq_refl (term93 c b)). Qed.
Lemma lem5274659 (s : real -> Prop) (c : real) (b : real) : (term282 s c b) = (term101 s c b).
Proof. exact (MK_COMB (@lem5274657 s c) (@lem5274658 c b)). Qed.
Lemma lem5274660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274661 (s : real -> Prop) (c : real) (b : real) : (term288 s c b) = (term289 s c b).
Proof. exact (MK_COMB (@lem5274660) (@lem5274659 s c b)). Qed.
Lemma lem5274662 (s : real -> Prop) (c : real) (x : real) : (term284 s c x) = (term81 s c x).
Proof. exact (eq_refl (term284 s c x)). Qed.
Lemma lem5274663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5274664 (s : real -> Prop) (c : real) (x : real) : (term290 s c x) = (term291 s c x).
Proof. exact (MK_COMB (@lem5274663) (@lem5274662 s c x)). Qed.
Lemma lem5274665 (c : real) (b : real) : (term93 c b) = (term93 c b).
Proof. exact (eq_refl (term93 c b)). Qed.
Lemma lem5274666 (s : real -> Prop) (x : real) (c : real) (b : real) : (term292 s x c b) = (term293 s x c b).
Proof. exact (MK_COMB (@lem5274664 s c x) (@lem5274665 c b)). Qed.
Lemma lem5274667 (s : real -> Prop) (c : real) (b : real) : (term294 s c b) = (term295 s c b).
Proof. exact (fun_ext (fun x : real => @lem5274666 s x c b)). Qed.
Lemma lem5274668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274669 (s : real -> Prop) (c : real) (b : real) : (term283 s c b) = (term296 s c b).
Proof. exact (MK_COMB (@lem5274668) (@lem5274667 s c b)). Qed.
Lemma lem5274670 (s : real -> Prop) (c : real) (b : real) : ((term282 s c b) = (term283 s c b)) = ((term101 s c b) = (term296 s c b)).
Proof. exact (MK_COMB (@lem5274661 s c b) (@lem5274669 s c b)). Qed.
Lemma lem5274671 (s : real -> Prop) (c : real) (b : real) : (term101 s c b) = (term296 s c b).
Proof. exact (EQ_MP (@lem5274670 s c b) (@lem5274651 s c b)). Qed.
Lemma lem5274672 (s : real -> Prop) (b : real) : (term114 s b) = (term297 s b).
Proof. exact (fun_ext (fun c : real => @lem5274671 s c b)). Qed.
Lemma lem5274673 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274674 (s : real -> Prop) (b : real) : (term125 s b) = (term298 s b).
Proof. exact (MK_COMB (@lem5274673) (@lem5274672 s b)). Qed.
Lemma lem5274687 (s : real -> Prop) (x : real) (c : real) (b : real) : (term293 s x c b) = (term293 s x c b).
Proof. exact (eq_refl (term293 s x c b)). Qed.
Lemma lem5274688 (s : real -> Prop) (c : real) (b : real) : (term295 s c b) = (term295 s c b).
Proof. exact (fun_ext (fun x : real => @lem5274687 s x c b)). Qed.
Lemma lem5274689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274690 (s : real -> Prop) (c : real) (b : real) : (term296 s c b) = (term296 s c b).
Proof. exact (MK_COMB (@lem5274689) (@lem5274688 s c b)). Qed.
Lemma lem5274691 (s : real -> Prop) (b : real) : (term297 s b) = (term297 s b).
Proof. exact (fun_ext (fun c : real => @lem5274690 s c b)). Qed.
Lemma lem5274692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274693 (s : real -> Prop) (b : real) : (term298 s b) = (term298 s b).
Proof. exact (MK_COMB (@lem5274692) (@lem5274691 s b)). Qed.
Lemma lem5274694 (s : real -> Prop) (b : real) : (term125 s b) = (term298 s b).
Proof. exact (TRANS (@lem5274674 s b) (@lem5274693 s b)). Qed.
Lemma lem5274695 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term298 s b.
Proof. exact (EQ_MP (@lem5274694 s b) (@lem5274545 s x' b h1)). Qed.
Lemma lem5274726 (b : real) (a : real) (x : real) : (term197 b a x) = (term197 b a x).
Proof. exact (eq_refl (term197 b a x)). Qed.
Lemma lem5274727 (b : real) (a : real) : (term205 b a) = (term205 b a).
Proof. exact (fun_ext (fun x : real => @lem5274726 b a x)). Qed.
Lemma lem5274728 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5274730 (b : real) (a : real) : (term206 b a) = (term206 b a).
Proof. exact (MK_COMB (@lem5274728) (@lem5274727 b a)). Qed.
Lemma lem5274731 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term206 b a.
Proof. exact (EQ_MP (@lem5274730 b a) (@lem5274552 s x b a h1)). Qed.
Lemma lem5274746 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term299 s x' b _69025.
Proof. exact (@lem5274626 s x' b h1 _69025). Qed.
Lemma lem5274747 (s : real -> Prop) (x' : real -> real) (_69025 : real) (b : real) : (term299 s x' b _69025) = (term273 s x' _69025 b).
Proof. exact (eq_refl (term299 s x' b _69025)). Qed.
Lemma lem5274748 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term273 s x' _69025 b.
Proof. exact (EQ_MP (@lem5274747 s x' _69025 b) (@lem5274746 _69025 s x' b h1)). Qed.
Lemma lem5274749 (_69026 : real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term284 s a _69026.
Proof. exact (@lem5274639 s b a x h1 _69026). Qed.
Lemma lem5274750 (s : real -> Prop) (a : real) (_69026 : real) : (term284 s a _69026) = (term81 s a _69026).
Proof. exact (eq_refl (term284 s a _69026)). Qed.
Lemma lem5274752 (_69027 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term300 s b _69027.
Proof. exact (@lem5274695 s x' b h1 _69027). Qed.
Lemma lem5274753 (s : real -> Prop) (_69027 : real) (b : real) : (term300 s b _69027) = (term296 s _69027 b).
Proof. exact (eq_refl (term300 s b _69027)). Qed.
Lemma lem5274754 (_69027 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term296 s _69027 b.
Proof. exact (EQ_MP (@lem5274753 s _69027 b) (@lem5274752 _69027 s x' b h1)). Qed.
Lemma lem5274755 (_69027 : real) (_69028 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term301 s _69027 b _69028.
Proof. exact (@lem5274754 _69027 s x' b h1 _69028). Qed.
Lemma lem5274756 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term301 s _69027 b _69028) = (term293 s _69028 _69027 b).
Proof. exact (eq_refl (term301 s _69027 b _69028)). Qed.
Lemma lem5274757 (_69028 : real) (_69027 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term293 s _69028 _69027 b.
Proof. exact (EQ_MP (@lem5274756 s _69028 _69027 b) (@lem5274755 _69027 _69028 s x' b h1)). Qed.
Lemma lem5274761 (_69030 : real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term302 b a _69030.
Proof. exact (@lem5274731 s x b a h1 _69030). Qed.
Lemma lem5274762 (b : real) (a : real) (_69030 : real) : (term302 b a _69030) = (term197 b a _69030).
Proof. exact (eq_refl (term302 b a _69030)). Qed.
Lemma lem5274787 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : x = b.
Proof. exact (proj1 (@lem5274548 s b a x h1)). Qed.
Lemma lem5274789 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term93 a x.
Proof. exact (proj2 (@lem5274548 s b a x h1)). Qed.
Lemma lem5274812 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term293 s _69028 _69027 b) = (term303 s _69028 _69027 b).
Proof. exact (@lem5273409 (term304 s _69028) (real_le _69027 _69028) (term93 _69027 b)). Qed.
Lemma lem5274813 (_69028 : real) (_69027 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term303 s _69028 _69027 b.
Proof. exact (EQ_MP (@lem5274812 s _69028 _69027 b) (@lem5274757 _69028 _69027 s x' b h1)). Qed.
Lemma lem5274819 (_69030 : real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term197 b a _69030.
Proof. exact (EQ_MP (@lem5274762 b a _69030) (@lem5274761 _69030 s x b a h1)). Qed.
Lemma lem5274823 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term93 a x.
Proof. exact (proj2 (@lem5274553 s x b a h1)). Qed.
Lemma lem5274877 (_69026 : real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term81 s a _69026.
Proof. exact (EQ_MP (@lem5274750 s a _69026) (@lem5274749 _69026 s b a x h1)). Qed.
Lemma lem5274878 (a : real) : (term305 a) = (term305 a).
Proof. exact (eq_refl (term305 a)). Qed.
Lemma lem5274879 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : (term306 a x) = (term306 a b).
Proof. exact (MK_COMB (@lem5274878 a) (@lem5274787 s b a x h1)). Qed.
Lemma lem5274880 (a : real) (b : real) : (term306 a b) = (term93 a b).
Proof. exact (eq_refl (term306 a b)). Qed.
Lemma lem5274881 (a : real) (x : real) : (term307 a x) = (term307 a x).
Proof. exact (eq_refl (term307 a x)). Qed.
Lemma lem5274882 (x : real) (a : real) (b : real) : ((term306 a x) = (term306 a b)) = ((term306 a x) = (term93 a b)).
Proof. exact (MK_COMB (@lem5274881 a x) (@lem5274880 a b)). Qed.
Lemma lem5274883 (a : real) (x : real) : (term306 a x) = (term93 a x).
Proof. exact (eq_refl (term306 a x)). Qed.
Lemma lem5274884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274885 (a : real) (x : real) : (term307 a x) = (term308 a x).
Proof. exact (MK_COMB (@lem5274884) (@lem5274883 a x)). Qed.
Lemma lem5274886 (a : real) (b : real) : (term93 a b) = (term93 a b).
Proof. exact (eq_refl (term93 a b)). Qed.
Lemma lem5274887 (x : real) (a : real) (b : real) : ((term306 a x) = (term93 a b)) = ((term93 a x) = (term93 a b)).
Proof. exact (MK_COMB (@lem5274885 a x) (@lem5274886 a b)). Qed.
Lemma lem5274888 (x : real) (a : real) (b : real) : ((term306 a x) = (term306 a b)) = ((term93 a x) = (term93 a b)).
Proof. exact (TRANS (@lem5274882 x a b) (@lem5274887 x a b)). Qed.
Lemma lem5274889 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : (term93 a x) = (term93 a b).
Proof. exact (EQ_MP (@lem5274888 x a b) (@lem5274879 s b a x h1)). Qed.
Lemma lem5274890 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term93 a b.
Proof. exact (EQ_MP (@lem5274889 s b a x h1) (@lem5274789 s b a x h1)). Qed.
Lemma lem5274904 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term309 s x' _69025 b.
Proof. exact (proj1 (@lem5274748 _69025 s x' b h1)). Qed.
Lemma lem5274918 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term310 x' _69025 b.
Proof. exact (proj2 (@lem5274748 _69025 s x' b h1)). Qed.
Lemma lem5274921 (a : real) (b : real) (h1 : term93 a b) : term93 a b.
Proof. exact (h1). Qed.
Lemma lem5274922 (a : real) (b : real) (h1 : term93 a b) : term311 a b.
Proof. exact (fun h0 : real_le a b => @lem5274921 a b h1). Qed.
Lemma lem5274924 (p : Prop) : (term312 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5274925 (a : real) (b : real) : (term311 a b) = (term93 a b).
Proof. exact (@lem5274924 (real_le a b)). Qed.
Lemma lem5274926 (a : real) (b : real) (h1 : term93 a b) : term93 a b.
Proof. exact (EQ_MP (@lem5274925 a b) (@lem5274922 a b h1)). Qed.
Lemma lem5274928 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5274931 (b : real) (s : real -> Prop) (x' : real -> real) (_69025 : real) : (term309 s x' _69025 b) = (term314 b s x' _69025).
Proof. exact (@lem5274928 (real_le _69025 b) (term274 s x' _69025)). Qed.
Lemma lem5274934 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term314 b s x' _69025.
Proof. exact (EQ_MP (@lem5274931 b s x' _69025) (@lem5274904 _69025 s x' b h1)). Qed.
Lemma lem5274935 (a : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term314 b s x' a.
Proof. exact (@lem5274934 a s x' b h1). Qed.
Lemma lem5274938 (a : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term93 a b) (h2 : term191 s x' b) : term274 s x' a.
Proof. exact (@lem5274935 a s x' b h2 (@lem5274926 a b h1)). Qed.
Lemma lem5274939 (a : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term93 a b) (h2 : term191 s x' b) : term315 s x' a.
Proof. exact (fun h0 : term316 s x' a => @lem5274938 a s x' b h1 h2). Qed.
Lemma lem5274941 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5274942 (s : real -> Prop) (x' : real -> real) (a : real) : (term315 s x' a) = (term274 s x' a).
Proof. exact (@lem5274941 (term274 s x' a)). Qed.
Lemma lem5274943 (a : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term93 a b) (h2 : term191 s x' b) : term274 s x' a.
Proof. exact (EQ_MP (@lem5274942 s x' a) (@lem5274939 a s x' b h1 h2)). Qed.
Lemma lem5274949 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5274950 (a : real) (s : real -> Prop) (_69026 : real) : (term81 s a _69026) = (term318 a s _69026).
Proof. exact (@lem5274949 (real_le a _69026) (term304 s _69026)). Qed.
Lemma lem5274956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5274957 (a : real) (s : real -> Prop) (_69026 : real) : (term319 s a _69026) = (term320 a s _69026).
Proof. exact (MK_COMB (@lem5274956) (@lem5274950 a s _69026)). Qed.
Lemma lem5274963 (a : real) (s : real -> Prop) (_69026 : real) : (term318 a s _69026) = (term318 a s _69026).
Proof. exact (eq_refl (term318 a s _69026)). Qed.
Lemma lem5274964 (a : real) (s : real -> Prop) (_69026 : real) : ((term81 s a _69026) = (term318 a s _69026)) = ((term318 a s _69026) = (term318 a s _69026)).
Proof. exact (MK_COMB (@lem5274957 a s _69026) (@lem5274963 a s _69026)). Qed.
Lemma lem5274966 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5274967 (x : Prop) : (x = x) = True.
Proof. exact (@lem5274966 Prop x). Qed.
Lemma lem5274968 (a : real) (s : real -> Prop) (_69026 : real) : ((term318 a s _69026) = (term318 a s _69026)) = True.
Proof. exact (@lem5274967 (term318 a s _69026)). Qed.
Lemma lem5274969 (a : real) (s : real -> Prop) (_69026 : real) : ((term81 s a _69026) = (term318 a s _69026)) = True.
Proof. exact (TRANS (@lem5274964 a s _69026) (@lem5274968 a s _69026)). Qed.
Lemma lem5274970 (a : real) (s : real -> Prop) (_69026 : real) : True = ((term81 s a _69026) = (term318 a s _69026)).
Proof. exact (SYM (@lem5274969 a s _69026)). Qed.
Lemma lem5274971 (a : real) (s : real -> Prop) (_69026 : real) : (term81 s a _69026) = (term318 a s _69026).
Proof. exact (EQ_MP (@lem5274970 a s _69026) (@lem0)). Qed.
Lemma lem5274972 (_69026 : real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term318 a s _69026.
Proof. exact (EQ_MP (@lem5274971 a s _69026) (@lem5274877 _69026 s b a x h1)). Qed.
Lemma lem5274974 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5274975 (s : real -> Prop) (a : real) (_69026 : real) : (term318 a s _69026) = (term321 s a _69026).
Proof. exact (@lem5274974 (term304 s _69026) (real_le a _69026)). Qed.
Lemma lem5274977 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5274978 (s : real -> Prop) (_69026 : real) : (term322 s _69026) = (s _69026).
Proof. exact (@lem5274977 (s _69026)). Qed.
Lemma lem5274979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5274980 (s : real -> Prop) (_69026 : real) : (term323 s _69026) = (term25 s _69026).
Proof. exact (MK_COMB (@lem5274979) (@lem5274978 s _69026)). Qed.
Lemma lem5274981 (a : real) (_69026 : real) : (real_le a _69026) = (real_le a _69026).
Proof. exact (eq_refl (real_le a _69026)). Qed.
Lemma lem5274982 (s : real -> Prop) (a : real) (_69026 : real) : (term321 s a _69026) = (term27 s a _69026).
Proof. exact (MK_COMB (@lem5274980 s _69026) (@lem5274981 a _69026)). Qed.
Lemma lem5274983 (s : real -> Prop) (a : real) (_69026 : real) : (term318 a s _69026) = (term27 s a _69026).
Proof. exact (TRANS (@lem5274975 s a _69026) (@lem5274982 s a _69026)). Qed.
Lemma lem5274986 (_69026 : real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term27 s a _69026.
Proof. exact (EQ_MP (@lem5274983 s a _69026) (@lem5274972 _69026 s b a x h1)). Qed.
Lemma lem5274987 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term324 s x' a.
Proof. exact (@lem5274986 (x' a) s b a x h1). Qed.
Lemma lem5274990 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term93 a b) (h2 : term191 s x' b) (h3 : term229 s b a x) : term325 x' a.
Proof. exact (@lem5274987 x' s b a x h3 (@lem5274943 a s x' b h1 h2)). Qed.
Lemma lem5274991 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term93 a b) (h2 : term191 s x' b) (h3 : term229 s b a x) : term326 x' a.
Proof. exact (fun h0 : term275 x' a => @lem5274990 x' s b a x h1 h2 h3). Qed.
Lemma lem5274993 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5274994 (x' : real -> real) (a : real) : (term326 x' a) = (term325 x' a).
Proof. exact (@lem5274993 (term325 x' a)). Qed.
Lemma lem5274995 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term93 a b) (h2 : term191 s x' b) (h3 : term229 s b a x) : term325 x' a.
Proof. exact (EQ_MP (@lem5274994 x' a) (@lem5274991 x' s b a x h1 h2 h3)). Qed.
Lemma lem5275001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5275002 (b : real) (x' : real -> real) (_69025 : real) : (term310 x' _69025 b) = (term327 b x' _69025).
Proof. exact (@lem5275001 (real_le _69025 b) (term275 x' _69025)). Qed.
Lemma lem5275008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5275009 (b : real) (x' : real -> real) (_69025 : real) : (term328 x' _69025 b) = (term329 b x' _69025).
Proof. exact (MK_COMB (@lem5275008) (@lem5275002 b x' _69025)). Qed.
Lemma lem5275015 (b : real) (x' : real -> real) (_69025 : real) : (term327 b x' _69025) = (term327 b x' _69025).
Proof. exact (eq_refl (term327 b x' _69025)). Qed.
Lemma lem5275016 (b : real) (x' : real -> real) (_69025 : real) : ((term310 x' _69025 b) = (term327 b x' _69025)) = ((term327 b x' _69025) = (term327 b x' _69025)).
Proof. exact (MK_COMB (@lem5275009 b x' _69025) (@lem5275015 b x' _69025)). Qed.
Lemma lem5275018 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5275019 (x : Prop) : (x = x) = True.
Proof. exact (@lem5275018 Prop x). Qed.
Lemma lem5275020 (b : real) (x' : real -> real) (_69025 : real) : ((term327 b x' _69025) = (term327 b x' _69025)) = True.
Proof. exact (@lem5275019 (term327 b x' _69025)). Qed.
Lemma lem5275021 (b : real) (x' : real -> real) (_69025 : real) : ((term310 x' _69025 b) = (term327 b x' _69025)) = True.
Proof. exact (TRANS (@lem5275016 b x' _69025) (@lem5275020 b x' _69025)). Qed.
Lemma lem5275022 (b : real) (x' : real -> real) (_69025 : real) : True = ((term310 x' _69025 b) = (term327 b x' _69025)).
Proof. exact (SYM (@lem5275021 b x' _69025)). Qed.
Lemma lem5275023 (b : real) (x' : real -> real) (_69025 : real) : (term310 x' _69025 b) = (term327 b x' _69025).
Proof. exact (EQ_MP (@lem5275022 b x' _69025) (@lem0)). Qed.
Lemma lem5275024 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term327 b x' _69025.
Proof. exact (EQ_MP (@lem5275023 b x' _69025) (@lem5274918 _69025 s x' b h1)). Qed.
Lemma lem5275026 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5275027 (x' : real -> real) (_69025 : real) (b : real) : (term327 b x' _69025) = (term330 x' _69025 b).
Proof. exact (@lem5275026 (term275 x' _69025) (real_le _69025 b)). Qed.
Lemma lem5275029 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5275030 (x' : real -> real) (_69025 : real) : (term331 x' _69025) = (term325 x' _69025).
Proof. exact (@lem5275029 (term325 x' _69025)). Qed.
Lemma lem5275031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275032 (x' : real -> real) (_69025 : real) : (term332 x' _69025) = (term333 x' _69025).
Proof. exact (MK_COMB (@lem5275031) (@lem5275030 x' _69025)). Qed.
Lemma lem5275033 (_69025 : real) (b : real) : (real_le _69025 b) = (real_le _69025 b).
Proof. exact (eq_refl (real_le _69025 b)). Qed.
Lemma lem5275034 (x' : real -> real) (_69025 : real) (b : real) : (term330 x' _69025 b) = (term334 x' _69025 b).
Proof. exact (MK_COMB (@lem5275032 x' _69025) (@lem5275033 _69025 b)). Qed.
Lemma lem5275035 (x' : real -> real) (_69025 : real) (b : real) : (term327 b x' _69025) = (term334 x' _69025 b).
Proof. exact (TRANS (@lem5275027 x' _69025 b) (@lem5275034 x' _69025 b)). Qed.
Lemma lem5275038 (_69025 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term334 x' _69025 b.
Proof. exact (EQ_MP (@lem5275035 x' _69025 b) (@lem5275024 _69025 s x' b h1)). Qed.
Lemma lem5275039 (a : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term334 x' a b.
Proof. exact (@lem5275038 a s x' b h1). Qed.
Lemma lem5275042 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term93 a b) (h2 : term191 s x' b) (h3 : term229 s b a x) : real_le a b.
Proof. exact (@lem5275039 a s x' b h2 (@lem5274995 x' s b a x h1 h2 h3)). Qed.
Lemma lem5275043 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term191 s x' b) (h2 : term229 s b a x) : term335 a b.
Proof. exact (fun h0 : term93 a b => @lem5275042 x' s b a x h0 h1 h2). Qed.
Lemma lem5275045 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275046 (a : real) (b : real) : (term335 a b) = (real_le a b).
Proof. exact (@lem5275045 (real_le a b)). Qed.
Lemma lem5275047 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term191 s x' b) (h2 : term229 s b a x) : real_le a b.
Proof. exact (EQ_MP (@lem5275046 a b) (@lem5275043 x' s b a x h1 h2)). Qed.
Lemma lem5275050 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5275052 (a : real) (b : real) : (term93 a b) = (term336 a b).
Proof. exact (@lem5275050 (real_le a b)). Qed.
Lemma lem5275055 (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term229 s b a x) : term336 a b.
Proof. exact (EQ_MP (@lem5275052 a b) (@lem5274890 s b a x h1)). Qed.
Lemma lem5275058 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term191 s x' b) (h2 : term229 s b a x) : False.
Proof. exact (@lem5275055 s b a x h2 (@lem5275047 x' s b a x h1 h2)). Qed.
Lemma lem5275059 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term191 s x' b) (h2 : term229 s b a x) : term337.
Proof. exact (fun h0 : ~ False => @lem5275058 x' s b a x h1 h2). Qed.
Lemma lem5275061 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275062 : term337 = False.
Proof. exact (@lem5275061 False). Qed.
Lemma lem5275106 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : s x.
Proof. exact (proj1 (@lem5274553 s x b a h1)). Qed.
Lemma lem5275107 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term338 s x.
Proof. exact (fun h0 : term304 s x => @lem5275106 s x b a h1). Qed.
Lemma lem5275109 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275110 (s : real -> Prop) (x : real) : (term338 s x) = (s x).
Proof. exact (@lem5275109 (s x)). Qed.
Lemma lem5275111 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : s x.
Proof. exact (EQ_MP (@lem5275110 s x) (@lem5275107 s x b a h1)). Qed.
Lemma lem5275113 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5275114 (b : real) : b = b.
Proof. exact (@lem5275113 b). Qed.
Lemma lem5275115 (b : real) : term339 b.
Proof. exact (fun h0 : term340 b => @lem5275114 b). Qed.
Lemma lem5275117 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275118 (b : real) : (term339 b) = (b = b).
Proof. exact (@lem5275117 (b = b)). Qed.
Lemma lem5275119 (b : real) : b = b.
Proof. exact (EQ_MP (@lem5275118 b) (@lem5275115 b)). Qed.
Lemma lem5275125 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5275126 (a : real) (_69030 : real) (b : real) : (term197 b a _69030) = (term341 a _69030 b).
Proof. exact (@lem5275125 (real_le a _69030) (term342 _69030 b)). Qed.
Lemma lem5275134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5275135 (a : real) (_69030 : real) (b : real) : (term343 b a _69030) = (term344 a _69030 b).
Proof. exact (MK_COMB (@lem5275134) (@lem5275126 a _69030 b)). Qed.
Lemma lem5275143 (a : real) (_69030 : real) (b : real) : (term341 a _69030 b) = (term341 a _69030 b).
Proof. exact (eq_refl (term341 a _69030 b)). Qed.
Lemma lem5275144 (a : real) (_69030 : real) (b : real) : ((term197 b a _69030) = (term341 a _69030 b)) = ((term341 a _69030 b) = (term341 a _69030 b)).
Proof. exact (MK_COMB (@lem5275135 a _69030 b) (@lem5275143 a _69030 b)). Qed.
Lemma lem5275146 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5275147 (x : Prop) : (x = x) = True.
Proof. exact (@lem5275146 Prop x). Qed.
Lemma lem5275148 (a : real) (_69030 : real) (b : real) : ((term341 a _69030 b) = (term341 a _69030 b)) = True.
Proof. exact (@lem5275147 (term341 a _69030 b)). Qed.
Lemma lem5275149 (a : real) (_69030 : real) (b : real) : ((term197 b a _69030) = (term341 a _69030 b)) = True.
Proof. exact (TRANS (@lem5275144 a _69030 b) (@lem5275148 a _69030 b)). Qed.
Lemma lem5275150 (a : real) (_69030 : real) (b : real) : True = ((term197 b a _69030) = (term341 a _69030 b)).
Proof. exact (SYM (@lem5275149 a _69030 b)). Qed.
Lemma lem5275151 (a : real) (_69030 : real) (b : real) : (term197 b a _69030) = (term341 a _69030 b).
Proof. exact (EQ_MP (@lem5275150 a _69030 b) (@lem0)). Qed.
Lemma lem5275152 (_69030 : real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term341 a _69030 b.
Proof. exact (EQ_MP (@lem5275151 a _69030 b) (@lem5274819 _69030 s x b a h1)). Qed.
Lemma lem5275154 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5275155 (b : real) (a : real) (_69030 : real) : (term341 a _69030 b) = (term345 b a _69030).
Proof. exact (@lem5275154 (term342 _69030 b) (real_le a _69030)). Qed.
Lemma lem5275157 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5275158 (_69030 : real) (b : real) : (term346 _69030 b) = (_69030 = b).
Proof. exact (@lem5275157 (_69030 = b)). Qed.
Lemma lem5275159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275160 (_69030 : real) (b : real) : (term347 _69030 b) = (term48 _69030 b).
Proof. exact (MK_COMB (@lem5275159) (@lem5275158 _69030 b)). Qed.
Lemma lem5275161 (a : real) (_69030 : real) : (real_le a _69030) = (real_le a _69030).
Proof. exact (eq_refl (real_le a _69030)). Qed.
Lemma lem5275162 (b : real) (a : real) (_69030 : real) : (term345 b a _69030) = (term50 b a _69030).
Proof. exact (MK_COMB (@lem5275160 _69030 b) (@lem5275161 a _69030)). Qed.
Lemma lem5275163 (b : real) (a : real) (_69030 : real) : (term341 a _69030 b) = (term50 b a _69030).
Proof. exact (TRANS (@lem5275155 b a _69030) (@lem5275162 b a _69030)). Qed.
Lemma lem5275166 (_69030 : real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term50 b a _69030.
Proof. exact (EQ_MP (@lem5275163 b a _69030) (@lem5275152 _69030 s x b a h1)). Qed.
Lemma lem5275167 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term348 a b.
Proof. exact (@lem5275166 b s x b a h1). Qed.
Lemma lem5275170 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : real_le a b.
Proof. exact (@lem5275167 s x b a h1 (@lem5275119 b)). Qed.
Lemma lem5275171 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term335 a b.
Proof. exact (fun h0 : term93 a b => @lem5275170 s x b a h1). Qed.
Lemma lem5275173 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275174 (a : real) (b : real) : (term335 a b) = (real_le a b).
Proof. exact (@lem5275173 (real_le a b)). Qed.
Lemma lem5275175 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : real_le a b.
Proof. exact (EQ_MP (@lem5275174 a b) (@lem5275171 s x b a h1)). Qed.
Lemma lem5275181 (q : Prop) (p : Prop) (r : Prop) : (term22 p q r) = (term22 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5275182 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term303 s _69028 _69027 b) = (term349 s _69028 _69027 b).
Proof. exact (@lem5275181 (real_le _69027 _69028) (term304 s _69028) (term93 _69027 b)). Qed.
Lemma lem5275198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5275199 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term350 s _69028 _69027 b) = (term351 s _69028 _69027 b).
Proof. exact (MK_COMB (@lem5275198) (@lem5275182 s _69028 _69027 b)). Qed.
Lemma lem5275215 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term349 s _69028 _69027 b) = (term349 s _69028 _69027 b).
Proof. exact (eq_refl (term349 s _69028 _69027 b)). Qed.
Lemma lem5275216 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : ((term303 s _69028 _69027 b) = (term349 s _69028 _69027 b)) = ((term349 s _69028 _69027 b) = (term349 s _69028 _69027 b)).
Proof. exact (MK_COMB (@lem5275199 s _69028 _69027 b) (@lem5275215 s _69028 _69027 b)). Qed.
Lemma lem5275218 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5275219 (x : Prop) : (x = x) = True.
Proof. exact (@lem5275218 Prop x). Qed.
Lemma lem5275220 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : ((term349 s _69028 _69027 b) = (term349 s _69028 _69027 b)) = True.
Proof. exact (@lem5275219 (term349 s _69028 _69027 b)). Qed.
Lemma lem5275221 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : ((term303 s _69028 _69027 b) = (term349 s _69028 _69027 b)) = True.
Proof. exact (TRANS (@lem5275216 s _69028 _69027 b) (@lem5275220 s _69028 _69027 b)). Qed.
Lemma lem5275222 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : True = ((term303 s _69028 _69027 b) = (term349 s _69028 _69027 b)).
Proof. exact (SYM (@lem5275221 s _69028 _69027 b)). Qed.
Lemma lem5275223 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term303 s _69028 _69027 b) = (term349 s _69028 _69027 b).
Proof. exact (EQ_MP (@lem5275222 s _69028 _69027 b) (@lem0)). Qed.
Lemma lem5275224 (_69028 : real) (_69027 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term349 s _69028 _69027 b.
Proof. exact (EQ_MP (@lem5275223 s _69028 _69027 b) (@lem5274813 _69028 _69027 s x' b h1)). Qed.
Lemma lem5275226 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5275227 (s : real -> Prop) (b : real) (_69027 : real) (_69028 : real) : (term349 s _69028 _69027 b) = (term352 s b _69027 _69028).
Proof. exact (@lem5275226 (term353 s _69028 _69027 b) (real_le _69027 _69028)). Qed.
Lemma lem5275229 (a : Prop) (b : Prop) : (term354 a b) = (term355 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5275230 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term356 s _69028 _69027 b) = (term357 s _69028 _69027 b).
Proof. exact (@lem5275229 (term304 s _69028) (term93 _69027 b)). Qed.
Lemma lem5275232 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5275233 (s : real -> Prop) (_69028 : real) : (term322 s _69028) = (s _69028).
Proof. exact (@lem5275232 (s _69028)). Qed.
Lemma lem5275234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5275235 (s : real -> Prop) (_69028 : real) : (term358 s _69028) = (term359 s _69028).
Proof. exact (MK_COMB (@lem5275234) (@lem5275233 s _69028)). Qed.
Lemma lem5275237 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5275238 (_69027 : real) (b : real) : (term360 _69027 b) = (real_le _69027 b).
Proof. exact (@lem5275237 (real_le _69027 b)). Qed.
Lemma lem5275239 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term357 s _69028 _69027 b) = (term361 s _69028 _69027 b).
Proof. exact (MK_COMB (@lem5275235 s _69028) (@lem5275238 _69027 b)). Qed.
Lemma lem5275240 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term356 s _69028 _69027 b) = (term361 s _69028 _69027 b).
Proof. exact (TRANS (@lem5275230 s _69028 _69027 b) (@lem5275239 s _69028 _69027 b)). Qed.
Lemma lem5275241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275242 (s : real -> Prop) (_69028 : real) (_69027 : real) (b : real) : (term362 s _69028 _69027 b) = (term363 s _69028 _69027 b).
Proof. exact (MK_COMB (@lem5275241) (@lem5275240 s _69028 _69027 b)). Qed.
Lemma lem5275243 (_69027 : real) (_69028 : real) : (real_le _69027 _69028) = (real_le _69027 _69028).
Proof. exact (eq_refl (real_le _69027 _69028)). Qed.
Lemma lem5275244 (s : real -> Prop) (b : real) (_69027 : real) (_69028 : real) : (term352 s b _69027 _69028) = (term364 s b _69027 _69028).
Proof. exact (MK_COMB (@lem5275242 s _69028 _69027 b) (@lem5275243 _69027 _69028)). Qed.
Lemma lem5275245 (s : real -> Prop) (b : real) (_69027 : real) (_69028 : real) : (term349 s _69028 _69027 b) = (term364 s b _69027 _69028).
Proof. exact (TRANS (@lem5275227 s b _69027 _69028) (@lem5275244 s b _69027 _69028)). Qed.
Lemma lem5275247 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term361 s x a b.
Proof. exact (conj (@lem5275111 s x b a h1) (@lem5275175 s x b a h1)). Qed.
Lemma lem5275249 (_69027 : real) (_69028 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term364 s b _69027 _69028.
Proof. exact (EQ_MP (@lem5275245 s b _69027 _69028) (@lem5275224 _69028 _69027 s x' b h1)). Qed.
Lemma lem5275250 (a : real) (x : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term364 s b a x.
Proof. exact (@lem5275249 a x s x' b h1). Qed.
Lemma lem5275253 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term246 s x b a) : real_le a x.
Proof. exact (@lem5275250 a x s x' b h1 (@lem5275247 s x b a h2)). Qed.
Lemma lem5275254 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term246 s x b a) : term335 a x.
Proof. exact (fun h0 : term93 a x => @lem5275253 x' s x b a h1 h2). Qed.
Lemma lem5275256 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275257 (a : real) (x : real) : (term335 a x) = (real_le a x).
Proof. exact (@lem5275256 (real_le a x)). Qed.
Lemma lem5275258 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term246 s x b a) : real_le a x.
Proof. exact (EQ_MP (@lem5275257 a x) (@lem5275254 x' s x b a h1 h2)). Qed.
Lemma lem5275261 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5275263 (a : real) (x : real) : (term93 a x) = (term336 a x).
Proof. exact (@lem5275261 (real_le a x)). Qed.
Lemma lem5275266 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term246 s x b a) : term336 a x.
Proof. exact (EQ_MP (@lem5275263 a x) (@lem5274823 s x b a h1)). Qed.
Lemma lem5275269 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term246 s x b a) : False.
Proof. exact (@lem5275266 s x b a h2 (@lem5275258 x' s x b a h1 h2)). Qed.
Lemma lem5275270 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term246 s x b a) : term337.
Proof. exact (fun h0 : ~ False => @lem5275269 x' s x b a h1 h2). Qed.
Lemma lem5275272 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5275273 : term337 = False.
Proof. exact (@lem5275272 False). Qed.
Lemma lem5275274 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term246 s x b a) : False.
Proof. exact (EQ_MP (@lem5275273) (@lem5275270 x' s x b a h1 h2)). Qed.
Lemma lem5275275 (x' : real -> real) (s : real -> Prop) (b : real) (a : real) (x : real) (h1 : term191 s x' b) (h2 : term229 s b a x) : False.
Proof. exact (EQ_MP (@lem5275062) (@lem5275059 x' s b a x h1 h2)). Qed.
Lemma lem5275276 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term269 s x b a) : False.
Proof. exact (or_elim (@lem5274482 s x b a h2) (fun h0 : term229 s b a x => @lem5275275 x' s b a x h1 h0) (fun h0 : term246 s x b a => @lem5275274 x' s x b a h1 h0)). Qed.
Lemma lem5275277 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term269 s x b a) : (term191 s x' b) = False.
Proof. exact (prop_ext (fun h3 : term191 s x' b => @lem5275276 x' s x b a h1 h2) (fun h3 : False => @lem5274543 s x' b h1)). Qed.
Lemma lem5275278 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term269 s x b a) : False.
Proof. exact (EQ_MP (@lem5275277 x' s x b a h1 h2) (@lem5274543 s x' b h1)). Qed.
Lemma lem5275279 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term269 s x b a) : (term269 s x b a) = False.
Proof. exact (prop_ext (fun h3 : term269 s x b a => @lem5275278 x' s x b a h1 h2) (fun h3 : False => @lem5274482 s x b a h2)). Qed.
Lemma lem5275280 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term191 s x' b) (h2 : term269 s x b a) : False.
Proof. exact (EQ_MP (@lem5275279 x' s x b a h1 h2) (@lem5274482 s x b a h2)). Qed.
Lemma lem5275281 (s : real -> Prop) (x : real) (b : real) (a : real) (h1 : term36 s b) (h2 : term269 s x b a) : False.
Proof. exact (ex_elim (@lem5274092 s b h1) (fun x' : real -> real => fun h0 : term193 s b x' => @lem5275280 x' s x b a h0 h2)). Qed.
Lemma lem5275282 (s : real -> Prop) (b : real) (a : real) (h1 : term36 s b) (h2 : term78 s b a) : False.
Proof. exact (ex_elim (@lem5274408 s b a h2) (fun x : real => fun h0 : term271 s b a x => @lem5275281 s x b a h1 h0)). Qed.
Lemma lem5275283 (s : real -> Prop) (b : real) (a : real) (h1 : term36 s b) (h2 : term78 s b a) : (term78 s b a) = False.
Proof. exact (prop_ext (fun h3 : term78 s b a => @lem5275282 s b a h1 h2) (fun h3 : False => @lem5273766 s b a h2)). Qed.
Lemma lem5275284 (s : real -> Prop) (b : real) (a : real) (h1 : term36 s b) (h2 : term78 s b a) : False.
Proof. exact (EQ_MP (@lem5275283 s b a h1 h2) (@lem5273766 s b a h2)). Qed.
Lemma lem5275285 (a : real) (s : real -> Prop) (b : real) (h1 : term36 s b) : term77 s b a.
Proof. exact (fun h0 : term78 s b a => @lem5275284 s b a h1 h0). Qed.
Lemma lem5275286 (a : real) (s : real -> Prop) (b : real) (h1 : term36 s b) : (term31 s a) = (term54 b a).
Proof. exact (EQ_MP (@lem5273765 s b a) (@lem5275285 a s b h1)). Qed.
Lemma lem5275291 (s : real -> Prop) (b : real) (h1 : term36 s b) : term58 s b.
Proof. exact (fun a : real => @lem5275286 a s b h1). Qed.
Lemma lem5275292 (s : real -> Prop) (b : real) : term60 s b.
Proof. exact (fun h0 : term36 s b => @lem5275291 s b h0). Qed.
Lemma lem5275297 (b : real) : term72 b.
Proof. exact (fun s : real -> Prop => @lem5275292 s b). Qed.
Lemma lem5275302 : term76.
Proof. exact (fun b : real => @lem5275297 b). Qed.
Lemma lem5275303 : term75.
Proof. exact (EQ_MP (@lem5273760) (@lem5275302)). Qed.
Lemma lem5275304 (b : real) : term365 b.
Proof. exact (@lem5275303 b). Qed.
Lemma lem5275305 (b : real) : (term365 b) = (term71 b).
Proof. exact (eq_refl (term365 b)). Qed.
Lemma lem5275306 (b : real) : term71 b.
Proof. exact (EQ_MP (@lem5275305 b) (@lem5275304 b)). Qed.
Lemma lem5275307 (b : real) (s : real -> Prop) : term366 b s.
Proof. exact (@lem5275306 b s). Qed.
Lemma lem5275308 (s : real -> Prop) (b : real) : (term366 b s) = (term62 s b).
Proof. exact (eq_refl (term366 b s)). Qed.
Lemma lem5275309 (s : real -> Prop) (b : real) : term62 s b.
Proof. exact (EQ_MP (@lem5275308 s b) (@lem5275307 b s)). Qed.
Lemma lem5275311 (s : real -> Prop) (b : real) : term62 s b.
Proof. exact (@lem5273599 s b (@lem5275309 s b)). Qed.
Lemma lem5275312 (s : real -> Prop) (b : real) (h1 : term63 s b) : False.
Proof. exact (@lem5275311 s b (@lem5273584 s b h1)). Qed.
Lemma lem5275313 (s : real -> Prop) (b : real) (h1 : term63 s b) : (term63 s b) = False.
Proof. exact (prop_ext (fun h2 : term63 s b => @lem5275312 s b h1) (fun h2 : False => @lem5273584 s b h1)). Qed.
Lemma lem5275314 (s : real -> Prop) (b : real) (h1 : term63 s b) : False.
Proof. exact (EQ_MP (@lem5275313 s b h1) (@lem5273584 s b h1)). Qed.
Lemma lem5275315 (s : real -> Prop) (b : real) : term62 s b.
Proof. exact (fun h0 : term63 s b => @lem5275314 s b h0). Qed.
Lemma lem5275316 (s : real -> Prop) (b : real) : term60 s b.
Proof. exact (EQ_MP (@lem5273583 s b) (@lem5275315 s b)). Qed.
Lemma lem5275318 (s : real -> Prop) (b : real) : term59 s b.
Proof. exact (EQ_MP (@lem5273579 s b) (@lem5275316 s b)). Qed.
Lemma lem5275319 (s : real -> Prop) (b : real) (h1 : term14 s b) : term57 s b.
Proof. exact (@lem5275318 s b (@lem5273390 s b h1)). Qed.
Lemma lem5275320 (s : real -> Prop) (b : real) (h1 : term14 s b) : (inf s) = (term8 b).
Proof. exact (@lem5273399 s b (@lem5275319 s b h1)). Qed.
Lemma lem5275321 (s : real -> Prop) (b : real) (h1 : term14 s b) : (inf s) = b.
Proof. exact (EQ_MP (@lem5273396 s b) (@lem5275320 s b h1)). Qed.
Lemma lem5275322 (s : real -> Prop) (b : real) (h1 : term14 s b) : (term14 s b) = ((inf s) = b).
Proof. exact (prop_ext (fun h2 : term14 s b => @lem5275321 s b h1) (fun h2 : (inf s) = b => @lem5273390 s b h1)). Qed.
Lemma lem5275323 (s : real -> Prop) (b : real) (h1 : term14 s b) : (inf s) = b.
Proof. exact (EQ_MP (@lem5275322 s b h1) (@lem5273390 s b h1)). Qed.
Lemma lem5275324 (s : real -> Prop) (b : real) : term367 s b.
Proof. exact (fun h0 : term14 s b => @lem5275323 s b h0). Qed.
Lemma lem5275329 (s : real -> Prop) : term368 s.
Proof. exact (fun b : real => @lem5275324 s b). Qed.
Lemma lem5275334 : term369.
Proof. exact (fun s : real -> Prop => @lem5275329 s). Qed.
