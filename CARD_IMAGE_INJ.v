Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_IMAGE_INJ_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3971277 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3971278 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3971279 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3971278 A x) (@lem3971277 A x)). Qed.
Lemma lem3971280 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3971282 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3971283 {A : Type'} (P : type686 A) (h1 : term3 A) : term4 A P.
Proof. exact (@lem3971282 A h1 P). Qed.
Lemma lem3971284 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem3971285 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (EQ_MP (@lem3971284 A P) (@lem3971283 A P h1)). Qed.
Lemma lem3971286 {A : Type'} (P : type686 A) (h1 : term6 A P) : term6 A P.
Proof. exact (h1). Qed.
Lemma lem3971287 {A : Type'} (P : type686 A) (h1 : term3 A) (h2 : term6 A P) : term7 A P.
Proof. exact (@lem3971285 A P h1 (@lem3971286 A P h2)). Qed.
Lemma lem3971288 {A : Type'} (P : type686 A) (h1 : term6 A P) : term8 A P.
Proof. exact (fun h0 : term3 A => @lem3971287 A P h0 h1). Qed.
Lemma lem3971289 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3971290 {A : Type'} (P : type686 A) (h1 : term3 A) (h2 : term6 A P) : term7 A P.
Proof. exact (@lem3971288 A P h2 (@lem3971289 A h1)). Qed.
Lemma lem3971291 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (fun h0 : term6 A P => @lem3971290 A P h1 h0). Qed.
Lemma lem3971292 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun P : type686 A => @lem3971291 A P h1). Qed.
Lemma lem3971293 {A : Type'} : term9 A.
Proof. exact (fun h0 : term3 A => @lem3971292 A h0). Qed.
Lemma lem3971294 {A : Type'} : term3 A.
Proof. exact (@lem3971293 A (@lem3558722 A)). Qed.
Lemma lem3971295 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem3971294 A P). Qed.
Lemma lem3971296 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem3971310 (a : Prop) : term10 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem3971311 (a : Prop) : (term10 a) = (term11 a).
Proof. exact (eq_refl (term10 a)). Qed.
Lemma lem3971312 (a : Prop) : term11 a.
Proof. exact (EQ_MP (@lem3971311 a) (@lem3971310 a)). Qed.
Lemma lem3971313 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem3971314 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem3971327 (b : Prop) (c : Prop) : (term12 b c) = (term12 b c).
Proof. exact (eq_refl (term12 b c)). Qed.
Lemma lem3971328 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term13 b c a) = (term14 b c).
Proof. exact (MK_COMB (@lem3971327 b c) (@lem3971313 a h1)). Qed.
Lemma lem3971329 (b : Prop) (c : Prop) : (term14 b c) = ((term15 b c) = (term16 b c)).
Proof. exact (eq_refl (term14 b c)). Qed.
Lemma lem3971330 (b : Prop) (c : Prop) (a : Prop) : (term17 b c a) = (term17 b c a).
Proof. exact (eq_refl (term17 b c a)). Qed.
Lemma lem3971331 (a : Prop) (b : Prop) (c : Prop) : ((term13 b c a) = (term14 b c)) = ((term13 b c a) = ((term15 b c) = (term16 b c))).
Proof. exact (MK_COMB (@lem3971330 b c a) (@lem3971329 b c)). Qed.
Lemma lem3971332 (b : Prop) (a : Prop) (c : Prop) : (term13 b c a) = ((term18 a b c) = (term19 b a c)).
Proof. exact (eq_refl (term13 b c a)). Qed.
Lemma lem3971333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3971334 (b : Prop) (a : Prop) (c : Prop) : (term17 b c a) = (term20 b a c).
Proof. exact (MK_COMB (@lem3971333) (@lem3971332 b a c)). Qed.
Lemma lem3971335 (b : Prop) (c : Prop) : ((term15 b c) = (term16 b c)) = ((term15 b c) = (term16 b c)).
Proof. exact (eq_refl ((term15 b c) = (term16 b c))). Qed.
Lemma lem3971336 (a : Prop) (b : Prop) (c : Prop) : ((term13 b c a) = ((term15 b c) = (term16 b c))) = (((term18 a b c) = (term19 b a c)) = ((term15 b c) = (term16 b c))).
Proof. exact (MK_COMB (@lem3971334 b a c) (@lem3971335 b c)). Qed.
Lemma lem3971337 (a : Prop) (b : Prop) (c : Prop) : ((term13 b c a) = (term14 b c)) = (((term18 a b c) = (term19 b a c)) = ((term15 b c) = (term16 b c))).
Proof. exact (TRANS (@lem3971331 a b c) (@lem3971336 a b c)). Qed.
Lemma lem3971338 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term18 a b c) = (term19 b a c)) = ((term15 b c) = (term16 b c)).
Proof. exact (EQ_MP (@lem3971337 a b c) (@lem3971328 b c a h1)). Qed.
Lemma lem3971339 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term15 b c) = (term16 b c)) = ((term18 a b c) = (term19 b a c)).
Proof. exact (SYM (@lem3971338 b c a h1)). Qed.
Lemma lem3971340 (b : Prop) (c : Prop) : (term12 b c) = (term12 b c).
Proof. exact (eq_refl (term12 b c)). Qed.
Lemma lem3971341 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term13 b c a) = (term21 b c).
Proof. exact (MK_COMB (@lem3971340 b c) (@lem3971314 a h1)). Qed.
Lemma lem3971342 (b : Prop) (c : Prop) : (term21 b c) = ((term22 b c) = (term23 b c)).
Proof. exact (eq_refl (term21 b c)). Qed.
Lemma lem3971343 (b : Prop) (c : Prop) (a : Prop) : (term17 b c a) = (term17 b c a).
Proof. exact (eq_refl (term17 b c a)). Qed.
Lemma lem3971344 (a : Prop) (b : Prop) (c : Prop) : ((term13 b c a) = (term21 b c)) = ((term13 b c a) = ((term22 b c) = (term23 b c))).
Proof. exact (MK_COMB (@lem3971343 b c a) (@lem3971342 b c)). Qed.
Lemma lem3971345 (b : Prop) (a : Prop) (c : Prop) : (term13 b c a) = ((term18 a b c) = (term19 b a c)).
Proof. exact (eq_refl (term13 b c a)). Qed.
Lemma lem3971346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3971347 (b : Prop) (a : Prop) (c : Prop) : (term17 b c a) = (term20 b a c).
Proof. exact (MK_COMB (@lem3971346) (@lem3971345 b a c)). Qed.
Lemma lem3971348 (b : Prop) (c : Prop) : ((term22 b c) = (term23 b c)) = ((term22 b c) = (term23 b c)).
Proof. exact (eq_refl ((term22 b c) = (term23 b c))). Qed.
Lemma lem3971349 (a : Prop) (b : Prop) (c : Prop) : ((term13 b c a) = ((term22 b c) = (term23 b c))) = (((term18 a b c) = (term19 b a c)) = ((term22 b c) = (term23 b c))).
Proof. exact (MK_COMB (@lem3971347 b a c) (@lem3971348 b c)). Qed.
Lemma lem3971350 (a : Prop) (b : Prop) (c : Prop) : ((term13 b c a) = (term21 b c)) = (((term18 a b c) = (term19 b a c)) = ((term22 b c) = (term23 b c))).
Proof. exact (TRANS (@lem3971344 a b c) (@lem3971349 a b c)). Qed.
Lemma lem3971351 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term18 a b c) = (term19 b a c)) = ((term22 b c) = (term23 b c)).
Proof. exact (EQ_MP (@lem3971350 a b c) (@lem3971341 b c a h1)). Qed.
Lemma lem3971352 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term22 b c) = (term23 b c)) = ((term18 a b c) = (term19 b a c)).
Proof. exact (SYM (@lem3971351 b c a h1)). Qed.
Lemma lem3971358 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3971359 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem3971358 b). Qed.
Lemma lem3971360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971361 (b : Prop) : (term24 b) = (imp b).
Proof. exact (MK_COMB (@lem3971360) (@lem3971359 b)). Qed.
Lemma lem3971362 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3971363 (b : Prop) (c : Prop) : (term15 b c) = (b -> c).
Proof. exact (MK_COMB (@lem3971361 b) (@lem3971362 c)). Qed.
Lemma lem3971366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3971367 (b : Prop) (c : Prop) : (term25 b c) = (term26 b c).
Proof. exact (MK_COMB (@lem3971366) (@lem3971363 b c)). Qed.
Lemma lem3971371 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3971372 (c : Prop) : (True -> c) = c.
Proof. exact (@lem3971371 c). Qed.
Lemma lem3971373 (b : Prop) : (imp b) = (imp b).
Proof. exact (eq_refl (imp b)). Qed.
Lemma lem3971374 (b : Prop) (c : Prop) : (term16 b c) = (b -> c).
Proof. exact (MK_COMB (@lem3971373 b) (@lem3971372 c)). Qed.
Lemma lem3971377 (b : Prop) (c : Prop) : ((term15 b c) = (term16 b c)) = ((b -> c) = (b -> c)).
Proof. exact (MK_COMB (@lem3971367 b c) (@lem3971374 b c)). Qed.
Lemma lem3971379 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3971380 (x : Prop) : (x = x) = True.
Proof. exact (@lem3971379 Prop x). Qed.
Lemma lem3971381 (b : Prop) (c : Prop) : ((b -> c) = (b -> c)) = True.
Proof. exact (@lem3971380 (b -> c)). Qed.
Lemma lem3971382 (b : Prop) (c : Prop) : ((term15 b c) = (term16 b c)) = True.
Proof. exact (TRANS (@lem3971377 b c) (@lem3971381 b c)). Qed.
Lemma lem3971383 (b : Prop) (c : Prop) : True = ((term15 b c) = (term16 b c)).
Proof. exact (SYM (@lem3971382 b c)). Qed.
Lemma lem3971384 (b : Prop) (c : Prop) : (term15 b c) = (term16 b c).
Proof. exact (EQ_MP (@lem3971383 b c) (@lem0)). Qed.
Lemma lem3971390 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3971391 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem3971390 b). Qed.
Lemma lem3971392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971393 (b : Prop) : (term27 b) = (imp False).
Proof. exact (MK_COMB (@lem3971392) (@lem3971391 b)). Qed.
Lemma lem3971394 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3971395 (b : Prop) (c : Prop) : (term22 b c) = (False -> c).
Proof. exact (MK_COMB (@lem3971393 b) (@lem3971394 c)). Qed.
Lemma lem3971397 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3971398 (c : Prop) : (False -> c) = True.
Proof. exact (@lem3971397 c). Qed.
Lemma lem3971399 (b : Prop) (c : Prop) : (term22 b c) = True.
Proof. exact (TRANS (@lem3971395 b c) (@lem3971398 c)). Qed.
Lemma lem3971400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3971401 (b : Prop) (c : Prop) : (term28 b c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3971400) (@lem3971399 b c)). Qed.
Lemma lem3971405 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3971406 (c : Prop) : (False -> c) = True.
Proof. exact (@lem3971405 c). Qed.
Lemma lem3971407 (b : Prop) : (imp b) = (imp b).
Proof. exact (eq_refl (imp b)). Qed.
Lemma lem3971408 (c : Prop) (b : Prop) : (term23 b c) = (b -> True).
Proof. exact (MK_COMB (@lem3971407 b) (@lem3971406 c)). Qed.
Lemma lem3971410 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3971411 (b : Prop) : (b -> True) = True.
Proof. exact (@lem3971410 b). Qed.
Lemma lem3971412 (b : Prop) (c : Prop) : (term23 b c) = True.
Proof. exact (TRANS (@lem3971408 c b) (@lem3971411 b)). Qed.
Lemma lem3971413 (b : Prop) (c : Prop) : ((term22 b c) = (term23 b c)) = (True = True).
Proof. exact (MK_COMB (@lem3971401 b c) (@lem3971412 b c)). Qed.
Lemma lem3971415 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3971416 : (True = True) = True.
Proof. exact (@lem3971415 True). Qed.
Lemma lem3971417 (b : Prop) (c : Prop) : ((term22 b c) = (term23 b c)) = True.
Proof. exact (TRANS (@lem3971413 b c) (@lem3971416)). Qed.
Lemma lem3971418 (b : Prop) (c : Prop) : True = ((term22 b c) = (term23 b c)).
Proof. exact (SYM (@lem3971417 b c)). Qed.
Lemma lem3971419 (b : Prop) (c : Prop) : (term22 b c) = (term23 b c).
Proof. exact (EQ_MP (@lem3971418 b c) (@lem0)). Qed.
Lemma lem3971420 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term18 a b c) = (term19 b a c).
Proof. exact (EQ_MP (@lem3971352 b c a h1) (@lem3971419 b c)). Qed.
Lemma lem3971421 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term18 a b c) = (term19 b a c).
Proof. exact (EQ_MP (@lem3971339 b c a h1) (@lem3971384 b c)). Qed.
Lemma lem3971430 (b : Prop) (a : Prop) (c : Prop) : (term18 a b c) = (term19 b a c).
Proof. exact (or_elim (@lem3971312 a) (fun h0 : a = True => @lem3971421 b c a h0) (fun h0 : a = False => @lem3971420 b c a h0)). Qed.
Lemma lem3971431 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term29 A B f s) = (term30 A B f s).
Proof. exact (@lem3971430 (@FINITE A s) (term31 A B s f) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3971445 (b : Prop) (a : Prop) (c : Prop) : (term18 a b c) = (term19 b a c).
Proof. exact (or_elim (@lem3971312 a) (fun h0 : a = True => @lem3971421 b c a h0) (fun h0 : a = False => @lem3971420 b c a h0)). Qed.
Lemma lem3971446 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term33 A B s f x y) = (term34 A B f s x y).
Proof. exact (@lem3971445 (term35 A B s x f y) (@IN A x s) (x = y)). Qed.
Lemma lem3971448 (b : Prop) (a : Prop) (c : Prop) : (term18 a b c) = (term19 b a c).
Proof. exact (or_elim (@lem3971312 a) (fun h0 : a = True => @lem3971421 b c a h0) (fun h0 : a = False => @lem3971420 b c a h0)). Qed.
Lemma lem3971449 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term34 A B f s x y) = (term36 A B f s x y).
Proof. exact (@lem3971448 ((f x) = (f y)) (@IN A y s) (term37 A s x y)). Qed.
Lemma lem3971454 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term33 A B s f x y) = (term36 A B f s x y).
Proof. exact (TRANS (@lem3971446 A B f s x y) (@lem3971449 A B f s x y)). Qed.
Lemma lem3971463 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term38 A B s f x) = (term39 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3971454 A B f s x y)). Qed.
Lemma lem3971464 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3971465 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term40 A B s f x) = (term41 A B f s x).
Proof. exact (MK_COMB (@lem3971464 A) (@lem3971463 A B f s x)). Qed.
Lemma lem3971470 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term42 A B s f) = (term43 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3971465 A B f s x)). Qed.
Lemma lem3971471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3971472 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term31 A B s f) = (term44 A B f s).
Proof. exact (MK_COMB (@lem3971471 A) (@lem3971470 A B f s)). Qed.
Lemma lem3971477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971478 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term45 A B s f) = (term46 A B f s).
Proof. exact (MK_COMB (@lem3971477) (@lem3971472 A B f s)). Qed.
Lemma lem3971481 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3971482 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term47 A B f s) = (term48 A B f s).
Proof. exact (MK_COMB (@lem3971478 A B f s) (@lem3971481 A B f s)). Qed.
Lemma lem3971485 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3971486 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term30 A B f s) = (term50 A B f s).
Proof. exact (MK_COMB (@lem3971485 A s) (@lem3971482 A B f s)). Qed.
Lemma lem3971489 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term29 A B f s) = (term50 A B f s).
Proof. exact (TRANS (@lem3971431 A B f s) (@lem3971486 A B f s)). Qed.
Lemma lem3971490 {A B : Type'} (f : A -> B) : (term51 A B f) = (term52 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3971489 A B f s)). Qed.
Lemma lem3971491 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3971492 {A B : Type'} (f : A -> B) : (term53 A B f) = (term54 A B f).
Proof. exact (MK_COMB (@lem3971491 A) (@lem3971490 A B f)). Qed.
Lemma lem3971497 {A B : Type'} (f : A -> B) : (term54 A B f) = (term53 A B f).
Proof. exact (SYM (@lem3971492 A B f)). Qed.
Lemma lem3971499 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem3971296 A P) (@lem3971295 A P)). Qed.
Lemma lem3971500 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (@lem3971499 A P). Qed.
Lemma lem3971501 {A B : Type'} (f : A -> B) : term55 A B f.
Proof. exact (@lem3971500 A (term56 A B f)). Qed.
Lemma lem3971502 {A B : Type'} (f : A -> B) : (term57 A B f) = (term58 A B f).
Proof. exact (eq_refl (term57 A B f)). Qed.
Lemma lem3971503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3971504 {A B : Type'} (f : A -> B) : (term59 A B f) = (term60 A B f).
Proof. exact (MK_COMB (@lem3971503) (@lem3971502 A B f)). Qed.
Lemma lem3971505 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term61 A B f s) = (term48 A B f s).
Proof. exact (eq_refl (term61 A B f s)). Qed.
Lemma lem3971506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3971507 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term62 A B f s) = (term63 A B f s).
Proof. exact (MK_COMB (@lem3971506) (@lem3971505 A B f s)). Qed.
Lemma lem3971508 {A : Type'} (x : A) (s : A -> Prop) : (term64 A x s) = (term64 A x s).
Proof. exact (eq_refl (term64 A x s)). Qed.
Lemma lem3971509 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term65 A B f x s) = (term66 A B f x s).
Proof. exact (MK_COMB (@lem3971507 A B f s) (@lem3971508 A x s)). Qed.
Lemma lem3971510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971511 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term67 A B f x s) = (term68 A B f x s).
Proof. exact (MK_COMB (@lem3971510) (@lem3971509 A B f x s)). Qed.
Lemma lem3971512 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term69 A B f x s) = (term70 A B f x s).
Proof. exact (eq_refl (term69 A B f x s)). Qed.
Lemma lem3971513 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term71 A B f x s) = (term72 A B f x s).
Proof. exact (MK_COMB (@lem3971511 A B f x s) (@lem3971512 A B f x s)). Qed.
Lemma lem3971514 {A B : Type'} (f : A -> B) (x : A) : (term73 A B f x) = (term74 A B f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3971513 A B f x s)). Qed.
Lemma lem3971515 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3971516 {A B : Type'} (f : A -> B) (x : A) : (term75 A B f x) = (term76 A B f x).
Proof. exact (MK_COMB (@lem3971515 A) (@lem3971514 A B f x)). Qed.
Lemma lem3971517 {A B : Type'} (f : A -> B) : (term77 A B f) = (term78 A B f).
Proof. exact (fun_ext (fun x : A => @lem3971516 A B f x)). Qed.
Lemma lem3971518 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3971519 {A B : Type'} (f : A -> B) : (term79 A B f) = (term80 A B f).
Proof. exact (MK_COMB (@lem3971518 A) (@lem3971517 A B f)). Qed.
Lemma lem3971520 {A B : Type'} (f : A -> B) : (term81 A B f) = (term82 A B f).
Proof. exact (MK_COMB (@lem3971504 A B f) (@lem3971519 A B f)). Qed.
Lemma lem3971521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971522 {A B : Type'} (f : A -> B) : (term83 A B f) = (term84 A B f).
Proof. exact (MK_COMB (@lem3971521) (@lem3971520 A B f)). Qed.
Lemma lem3971523 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term61 A B f s) = (term48 A B f s).
Proof. exact (eq_refl (term61 A B f s)). Qed.
Lemma lem3971524 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3971525 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term85 A B f s) = (term50 A B f s).
Proof. exact (MK_COMB (@lem3971524 A s) (@lem3971523 A B f s)). Qed.
Lemma lem3971526 {A B : Type'} (f : A -> B) : (term86 A B f) = (term52 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3971525 A B f s)). Qed.
Lemma lem3971527 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3971528 {A B : Type'} (f : A -> B) : (term87 A B f) = (term54 A B f).
Proof. exact (MK_COMB (@lem3971527 A) (@lem3971526 A B f)). Qed.
Lemma lem3971529 {A B : Type'} (f : A -> B) : (term55 A B f) = (term88 A B f).
Proof. exact (MK_COMB (@lem3971522 A B f) (@lem3971528 A B f)). Qed.
Lemma lem3971530 {A B : Type'} (f : A -> B) : term88 A B f.
Proof. exact (EQ_MP (@lem3971529 A B f) (@lem3971501 A B f)). Qed.
Lemma lem3971552 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3971280 A x (@lem3971279 A x)). Qed.
Lemma lem3971553 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3971552 A x). Qed.
Lemma lem3971554 {A : Type'} (y : A) : (@IN A y (@EMPTY A)) = False.
Proof. exact (@lem3971553 A y). Qed.
Lemma lem3971555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971556 {A : Type'} (y : A) : (term89 A y) = (imp False).
Proof. exact (MK_COMB (@lem3971555) (@lem3971554 A y)). Qed.
Lemma lem3971560 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3971280 A x (@lem3971279 A x)). Qed.
Lemma lem3971561 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3971560 A x). Qed.
Lemma lem3971562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971563 {A : Type'} (x : A) : (term89 A x) = (imp False).
Proof. exact (MK_COMB (@lem3971562) (@lem3971561 A x)). Qed.
Lemma lem3971566 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3971567 {A : Type'} (x : A) (y : A) : (term90 A x y) = (term91 A x y).
Proof. exact (MK_COMB (@lem3971563 A x) (@lem3971566 A x y)). Qed.
Lemma lem3971569 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3971570 {A : Type'} (x : A) (y : A) : (term91 A x y) = True.
Proof. exact (@lem3971569 (x = y)). Qed.
Lemma lem3971571 {A : Type'} (x : A) (y : A) : (term90 A x y) = True.
Proof. exact (TRANS (@lem3971567 A x y) (@lem3971570 A x y)). Qed.
Lemma lem3971572 {A : Type'} (x : A) (y : A) : (term92 A x y) = (False -> True).
Proof. exact (MK_COMB (@lem3971556 A y) (@lem3971571 A x y)). Qed.
Lemma lem3971574 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3971575 : (False -> True) = True.
Proof. exact (@lem3971574 True). Qed.
Lemma lem3971576 {A : Type'} (x : A) (y : A) : (term92 A x y) = True.
Proof. exact (TRANS (@lem3971572 A x y) (@lem3971575)). Qed.
Lemma lem3971577 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term93 A B x f y) = (term93 A B x f y).
Proof. exact (eq_refl (term93 A B x f y)). Qed.
Lemma lem3971578 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term94 A B f x y) = (term95 A B x f y).
Proof. exact (MK_COMB (@lem3971577 A B x f y) (@lem3971576 A x y)). Qed.
Lemma lem3971582 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3971583 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term95 A B x f y) = True.
Proof. exact (@lem3971582 ((f x) = (f y))). Qed.
Lemma lem3971584 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term94 A B f x y) = True.
Proof. exact (TRANS (@lem3971578 A B x f y) (@lem3971583 A B x f y)). Qed.
Lemma lem3971585 {A B : Type'} (f : A -> B) (x : A) : (term96 A B f x) = (term97 A).
Proof. exact (fun_ext (fun y : A => @lem3971584 A B f x y)). Qed.
Lemma lem3971586 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3971587 {A B : Type'} (f : A -> B) (x : A) : (term98 A B f x) = (term99 A).
Proof. exact (MK_COMB (@lem3971586 A) (@lem3971585 A B f x)). Qed.
Lemma lem3971589 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3971590 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (@lem3971589 A t). Qed.
Lemma lem3971591 {A : Type'} : (term99 A) = True.
Proof. exact (@lem3971590 A True). Qed.
Lemma lem3971592 {A B : Type'} (f : A -> B) (x : A) : (term98 A B f x) = True.
Proof. exact (TRANS (@lem3971587 A B f x) (@lem3971591 A)). Qed.
Lemma lem3971593 {A B : Type'} (f : A -> B) : (term101 A B f) = (term97 A).
Proof. exact (fun_ext (fun x : A => @lem3971592 A B f x)). Qed.
Lemma lem3971594 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3971595 {A B : Type'} (f : A -> B) : (term102 A B f) = (term99 A).
Proof. exact (MK_COMB (@lem3971594 A) (@lem3971593 A B f)). Qed.
Lemma lem3971597 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3971598 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (@lem3971597 A t). Qed.
Lemma lem3971599 {A : Type'} : (term99 A) = True.
Proof. exact (@lem3971598 A True). Qed.
Lemma lem3971600 {A B : Type'} (f : A -> B) : (term102 A B f) = True.
Proof. exact (TRANS (@lem3971595 A B f) (@lem3971599 A)). Qed.
Lemma lem3971601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3971602 {A B : Type'} (f : A -> B) : (term103 A B f) = (imp True).
Proof. exact (MK_COMB (@lem3971601) (@lem3971600 A B f)). Qed.
Lemma lem3971606 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem3971607 {A B : Type'} (f : A -> B) : (@IMAGE A B f (@EMPTY A)) = (@EMPTY B).
Proof. exact (@lem3971606 A B f). Qed.
Lemma lem3971608 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem3971609 {A B : Type'} (f : A -> B) : (term104 A B f) = (@CARD B (@EMPTY B)).
Proof. exact (MK_COMB (@lem3971608 B) (@lem3971607 A B f)). Qed.
Lemma lem3971610 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3971611 {A B : Type'} (f : A -> B) : (term105 A B f) = (term106 B).
Proof. exact (MK_COMB (@lem3971610) (@lem3971609 A B f)). Qed.
Lemma lem3971612 {A : Type'} : (@CARD A (@EMPTY A)) = (@CARD A (@EMPTY A)).
Proof. exact (eq_refl (@CARD A (@EMPTY A))). Qed.
Lemma lem3971613 {A B : Type'} (f : A -> B) : ((term104 A B f) = (@CARD A (@EMPTY A))) = ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A))).
Proof. exact (MK_COMB (@lem3971611 A B f) (@lem3971612 A)). Qed.
Lemma lem3971616 {A B : Type'} (f : A -> B) : (term58 A B f) = (term107 A B).
Proof. exact (MK_COMB (@lem3971602 A B f) (@lem3971613 A B f)). Qed.
Lemma lem3971618 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3971619 {A B : Type'} : (term107 A B) = ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A))).
Proof. exact (@lem3971618 ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A)))). Qed.
Lemma lem3971622 {A B : Type'} (f : A -> B) : (term58 A B f) = ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A))).
Proof. exact (TRANS (@lem3971616 A B f) (@lem3971619 A B)). Qed.
Lemma lem3971623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3971624 {A B : Type'} (f : A -> B) : (term60 A B f) = (term108 A B).
Proof. exact (MK_COMB (@lem3971623) (@lem3971622 A B f)). Qed.
Lemma lem3971688 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term109 _87477 _87481 f x s) = (term110 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem3971689 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term109 A B f x s) = (term110 A B x f s).
Proof. exact (@lem3971688 A B x f s). Qed.
Lemma lem3971690 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem3971691 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term111 A B f x s) = (term112 A B x f s).
Proof. exact (MK_COMB (@lem3971690 B) (@lem3971689 A B x f s)). Qed.
Lemma lem3971692 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3971693 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term113 A B f x s) = (term114 A B x f s).
Proof. exact (MK_COMB (@lem3971692) (@lem3971691 A B x f s)). Qed.
Lemma lem3971694 {A : Type'} (x : A) (s : A -> Prop) : (term115 A x s) = (term115 A x s).
Proof. exact (eq_refl (term115 A x s)). Qed.
Lemma lem3971695 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : ((term111 A B f x s) = (term115 A x s)) = ((term112 A B x f s) = (term115 A x s)).
Proof. exact (MK_COMB (@lem3971693 A B x f s) (@lem3971694 A x s)). Qed.
Lemma lem3971698 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term116 A B f x s) = (term116 A B f x s).
Proof. exact (eq_refl (term116 A B f x s)). Qed.
Lemma lem3971699 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term70 A B f x s) = (term117 A B f x s).
Proof. exact (MK_COMB (@lem3971698 A B f x s) (@lem3971695 A B f x s)). Qed.
Lemma lem3971702 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term68 A B f x s) = (term68 A B f x s).
Proof. exact (eq_refl (term68 A B f x s)). Qed.
Lemma lem3971703 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term72 A B f x s) = (term118 A B f x s).
Proof. exact (MK_COMB (@lem3971702 A B f x s) (@lem3971699 A B f x s)). Qed.
Lemma lem3971706 {A B : Type'} (f : A -> B) (x : A) : (term74 A B f x) = (term119 A B f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3971703 A B f x s)). Qed.
Lemma lem3971707 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3971708 {A B : Type'} (f : A -> B) (x : A) : (term76 A B f x) = (term120 A B f x).
Proof. exact (MK_COMB (@lem3971707 A) (@lem3971706 A B f x)). Qed.
Lemma lem3971713 {A B : Type'} (f : A -> B) : (term78 A B f) = (term121 A B f).
Proof. exact (fun_ext (fun x : A => @lem3971708 A B f x)). Qed.
Lemma lem3971714 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3971715 {A B : Type'} (f : A -> B) : (term80 A B f) = (term122 A B f).
Proof. exact (MK_COMB (@lem3971714 A) (@lem3971713 A B f)). Qed.
Lemma lem3971720 {A B : Type'} (f : A -> B) : (term82 A B f) = (term123 A B f).
Proof. exact (MK_COMB (@lem3971624 A B f) (@lem3971715 A B f)). Qed.
Lemma lem3971723 {A B : Type'} (f : A -> B) : (term123 A B f) = (term82 A B f).
Proof. exact (SYM (@lem3971720 A B f)). Qed.
Lemma lem3971724 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term66 A B f x s) : term66 A B f x s.
Proof. exact (h1). Qed.
Lemma lem3971725 {A : Type'} (x : A) (s : A -> Prop) (h1 : term64 A x s) : term64 A x s.
Proof. exact (h1). Qed.
Lemma lem3971726 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term48 A B f s.
Proof. exact (h1). Qed.
Lemma lem3971727 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3971728 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term124 A x s.
Proof. exact (h1). Qed.
Lemma lem3971729 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term125 A B f x s.
Proof. exact (h1). Qed.
Lemma lem3971772 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3971773 {B : Type'} : (@CARD B (@EMPTY B)) = (NUMERAL 0).
Proof. exact (@lem3971772 B). Qed.
Lemma lem3971774 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3971775 {B : Type'} : (term106 B) = term126.
Proof. exact (MK_COMB (@lem3971774) (@lem3971773 B)). Qed.
Lemma lem3971777 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3971778 {A B : Type'} : ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3971775 B) (@lem3971777 A)). Qed.
Lemma lem3971780 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3971781 (x : nat) : (x = x) = True.
Proof. exact (@lem3971780 nat x). Qed.
Lemma lem3971782 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem3971781 (NUMERAL 0)). Qed.
Lemma lem3971783 {A B : Type'} : ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3971778 A B) (@lem3971782)). Qed.
Lemma lem3971784 {A B : Type'} : True = ((@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A))).
Proof. exact (SYM (@lem3971783 A B)). Qed.
Lemma lem3971785 {A B : Type'} : (@CARD B (@EMPTY B)) = (@CARD A (@EMPTY A)).
Proof. exact (EQ_MP (@lem3971784 A B) (@lem0)). Qed.
Lemma lem3971786 {A B : Type'} (y : B) : term127 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3971787 {A B : Type'} (y : B) : (term127 A B y) = (term128 A B y).
Proof. exact (eq_refl (term127 A B y)). Qed.
Lemma lem3971788 {A B : Type'} (y : B) : term128 A B y.
Proof. exact (EQ_MP (@lem3971787 A B y) (@lem3971786 A B y)). Qed.
Lemma lem3971789 {A B : Type'} (y : B) (s : A -> Prop) : term129 A B y s.
Proof. exact (@lem3971788 A B y s). Qed.
Lemma lem3971790 {A B : Type'} (y : B) (s : A -> Prop) : (term129 A B y s) = (term130 A B y s).
Proof. exact (eq_refl (term129 A B y s)). Qed.
Lemma lem3971791 {A B : Type'} (y : B) (s : A -> Prop) : term130 A B y s.
Proof. exact (EQ_MP (@lem3971790 A B y s) (@lem3971789 A B y s)). Qed.
Lemma lem3971792 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term131 A B y s f.
Proof. exact (@lem3971791 A B y s f). Qed.
Lemma lem3971793 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term131 A B y s f) = ((term132 A B y f s) = (term133 A B y f s)).
Proof. exact (eq_refl (term131 A B y s f)). Qed.
Lemma lem3971795 {A B : Type'} (f : A -> B) : term134 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3971796 {A B : Type'} (f : A -> B) : (term134 A B f) = (term135 A B f).
Proof. exact (eq_refl (term134 A B f)). Qed.
Lemma lem3971797 {A B : Type'} (f : A -> B) : term135 A B f.
Proof. exact (EQ_MP (@lem3971796 A B f) (@lem3971795 A B f)). Qed.
Lemma lem3971798 {A B : Type'} (f : A -> B) (s : A -> Prop) : term136 A B f s.
Proof. exact (@lem3971797 A B f s). Qed.
Lemma lem3971799 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term136 A B f s) = (term137 A B f s).
Proof. exact (eq_refl (term136 A B f s)). Qed.
Lemma lem3971800 {A B : Type'} (f : A -> B) (s : A -> Prop) : term137 A B f s.
Proof. exact (EQ_MP (@lem3971799 A B f s) (@lem3971798 A B f s)). Qed.
Lemma lem3971801 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3971802 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term138 A B f s.
Proof. exact (@lem3971800 A B f s (@lem3971801 A s h1)). Qed.
Lemma lem3971803 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term138 A B f s) = ((term138 A B f s) = True).
Proof. exact (@lem7 (term138 A B f s)). Qed.
Lemma lem3971804 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term138 A B f s) = True.
Proof. exact (EQ_MP (@lem3971803 A B f s) (@lem3971802 A B f s h1)). Qed.
Lemma lem3971810 {A : Type'} : term139 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3971811 {A : Type'} (x : A) : term140 A x.
Proof. exact (@lem3971810 A x). Qed.
Lemma lem3971812 {A : Type'} (x : A) : (term140 A x) = (term141 A x).
Proof. exact (eq_refl (term140 A x)). Qed.
Lemma lem3971813 {A : Type'} (x : A) : term141 A x.
Proof. exact (EQ_MP (@lem3971812 A x) (@lem3971811 A x)). Qed.
Lemma lem3971814 {A : Type'} (x : A) (s : A -> Prop) : term142 A x s.
Proof. exact (@lem3971813 A x s). Qed.
Lemma lem3971815 {A : Type'} (x : A) (s : A -> Prop) : (term142 A x s) = (term143 A x s).
Proof. exact (eq_refl (term142 A x s)). Qed.
Lemma lem3971816 {A : Type'} (x : A) (s : A -> Prop) : term143 A x s.
Proof. exact (EQ_MP (@lem3971815 A x s) (@lem3971814 A x s)). Qed.
Lemma lem3971817 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3971818 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term115 A x s) = (term144 A x s).
Proof. exact (@lem3971816 A x s (@lem3971817 A s h1)). Qed.
Lemma lem3971832 {A : Type'} (x : A) (s : A -> Prop) : term145 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3971834 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3971878 {A : Type'} (x : A) (s : A -> Prop) : term143 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3971818 A x s h0). Qed.
Lemma lem3971879 {B : Type'} (x : B) (s : B -> Prop) : term143 B x s.
Proof. exact (@lem3971878 B x s). Qed.
Lemma lem3971880 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term146 A B x f s.
Proof. exact (@lem3971879 B (f x) (@IMAGE A B f s)). Qed.
Lemma lem3971882 {A B : Type'} (f : A -> B) (s : A -> Prop) : term147 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3971804 A B f s h0). Qed.
Lemma lem3971883 {A B : Type'} (f : A -> B) (s : A -> Prop) : term147 A B f s.
Proof. exact (@lem3971882 A B f s). Qed.
Lemma lem3971885 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3971834 A s) (@lem3971727 A s h1)). Qed.
Lemma lem3971890 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3971885 A s h1)). Qed.
Lemma lem3971891 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3971890 A s h1) (@lem0)). Qed.
Lemma lem3971892 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term138 A B f s) = True.
Proof. exact (@lem3971883 A B f s (@lem3971891 A s h1)). Qed.
Lemma lem3971897 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : True = (term138 A B f s).
Proof. exact (SYM (@lem3971892 A B f s h1)). Qed.
Lemma lem3971898 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term138 A B f s.
Proof. exact (EQ_MP (@lem3971897 A B f s h1) (@lem0)). Qed.
Lemma lem3971899 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term112 A B x f s) = (term148 A B x f s).
Proof. exact (@lem3971880 A B x f s (@lem3971898 A B f s h1)). Qed.
Lemma lem3971905 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term149 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3971906 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term150 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3971905 _2963 g t e g' t' e'). Qed.
Lemma lem3971907 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term151 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3971906 _2963 g t e g' t'). Qed.
Lemma lem3971908 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term152 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3971907 _2963 g t e g'). Qed.
Lemma lem3971909 (g : Prop) (t : nat) (e : nat) : term153 g t e.
Proof. exact (@lem3971908 nat g t e). Qed.
Lemma lem3971910 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term154 A B x f s.
Proof. exact (@lem3971909 (term155 A B x f s) (term32 A B f s) (term156 A B f s)). Qed.
Lemma lem3971911 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) : term157 A B x f s g'.
Proof. exact (@lem3971910 A B x f s g'). Qed.
Lemma lem3971912 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) : (term157 A B x f s g') = (term158 A B x f s g').
Proof. exact (eq_refl (term157 A B x f s g')). Qed.
Lemma lem3971913 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) : term158 A B x f s g'.
Proof. exact (EQ_MP (@lem3971912 A B x f s g') (@lem3971911 A B x f s g')). Qed.
Lemma lem3971914 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) (t' : nat) : term159 A B x f s g' t'.
Proof. exact (@lem3971913 A B x f s g' t'). Qed.
Lemma lem3971915 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) (t' : nat) : (term159 A B x f s g' t') = (term160 A B x f s g' t').
Proof. exact (eq_refl (term159 A B x f s g' t')). Qed.
Lemma lem3971916 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) (t' : nat) : term160 A B x f s g' t'.
Proof. exact (EQ_MP (@lem3971915 A B x f s g' t') (@lem3971914 A B x f s g' t')). Qed.
Lemma lem3971917 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term161 A B x f s g' t' e'.
Proof. exact (@lem3971916 A B x f s g' t' e'). Qed.
Lemma lem3971918 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term161 A B x f s g' t' e') = (term162 A B x f s g' t' e').
Proof. exact (eq_refl (term161 A B x f s g' t' e')). Qed.
Lemma lem3971919 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term162 A B x f s g' t' e'.
Proof. exact (EQ_MP (@lem3971918 A B x f s g' t' e') (@lem3971917 A B x f s g' t' e')). Qed.
Lemma lem3971921 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term132 A B y f s) = (term133 A B y f s).
Proof. exact (EQ_MP (@lem3971793 A B y f s) (@lem3971792 A B y s f)). Qed.
Lemma lem3971922 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term132 A B y f s) = (term133 A B y f s).
Proof. exact (@lem3971921 A B y f s). Qed.
Lemma lem3971923 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term155 A B x f s) = (term163 A B x f s).
Proof. exact (@lem3971922 A B (f x) f s). Qed.
Lemma lem3972010 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (t' : nat) (e' : nat) : term164 A B x f s t' e'.
Proof. exact (@lem3971919 A B x f s (term163 A B x f s) t' e'). Qed.
Lemma lem3972011 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (t' : nat) (e' : nat) : term165 A B x f s t' e'.
Proof. exact (@lem3972010 A B x f s t' e' (@lem3971923 A B x f s)). Qed.
Lemma lem3973042 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term32 A B f s) = (term32 A B f s).
Proof. exact (eq_refl (term32 A B f s)). Qed.
Lemma lem3973043 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term166 A B x f s.
Proof. exact (fun h0 : term163 A B x f s => @lem3973042 A B f s). Qed.
Lemma lem3973044 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (e' : nat) : term167 A B x f s e'.
Proof. exact (@lem3972011 A B x f s (term32 A B f s) e'). Qed.
Lemma lem3973045 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (e' : nat) : term168 A B x f s e'.
Proof. exact (@lem3973044 A B x f s e' (@lem3973043 A B x f s)). Qed.
Lemma lem3974084 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term156 A B f s) = (term156 A B f s).
Proof. exact (eq_refl (term156 A B f s)). Qed.
Lemma lem3974085 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term169 A B x f s.
Proof. exact (fun h0 : term170 A B x f s => @lem3974084 A B f s). Qed.
Lemma lem3974086 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term171 A B x f s.
Proof. exact (@lem3973045 A B x f s (term156 A B f s)). Qed.
Lemma lem3974087 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term148 A B x f s) = (term172 A B x f s).
Proof. exact (@lem3974086 A B x f s (@lem3974085 A B x f s)). Qed.
Lemma lem3978433 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term112 A B x f s) = (term172 A B x f s).
Proof. exact (TRANS (@lem3971899 A B x f s h1) (@lem3974087 A B x f s)). Qed.
Lemma lem3978434 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3978435 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term114 A B x f s) = (term173 A B x f s).
Proof. exact (MK_COMB (@lem3978434) (@lem3978433 A B x f s h1)). Qed.
Lemma lem3982790 {A : Type'} (x : A) (s : A -> Prop) : term143 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3971818 A x s h0). Qed.
Lemma lem3982791 {A : Type'} (x : A) (s : A -> Prop) : term143 A x s.
Proof. exact (@lem3982790 A x s). Qed.
Lemma lem3982793 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3971834 A s) (@lem3971727 A s h1)). Qed.
Lemma lem3982798 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3982793 A s h1)). Qed.
Lemma lem3982799 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3982798 A s h1) (@lem0)). Qed.
Lemma lem3982800 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term115 A x s) = (term144 A x s).
Proof. exact (@lem3982791 A x s (@lem3982799 A s h1)). Qed.
Lemma lem3982806 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term149 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3982807 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term150 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3982806 _2963 g t e g' t' e'). Qed.
Lemma lem3982808 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term151 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3982807 _2963 g t e g' t'). Qed.
Lemma lem3982809 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term152 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3982808 _2963 g t e g'). Qed.
Lemma lem3982810 (g : Prop) (t : nat) (e : nat) : term153 g t e.
Proof. exact (@lem3982809 nat g t e). Qed.
Lemma lem3982811 {A : Type'} (x : A) (s : A -> Prop) : term174 A x s.
Proof. exact (@lem3982810 (@IN A x s) (@CARD A s) (term175 A s)). Qed.
Lemma lem3982812 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term176 A x s g'.
Proof. exact (@lem3982811 A x s g'). Qed.
Lemma lem3982813 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : (term176 A x s g') = (term177 A x s g').
Proof. exact (eq_refl (term176 A x s g')). Qed.
Lemma lem3982814 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term177 A x s g'.
Proof. exact (EQ_MP (@lem3982813 A x s g') (@lem3982812 A x s g')). Qed.
Lemma lem3982815 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term178 A x s g' t'.
Proof. exact (@lem3982814 A x s g' t'). Qed.
Lemma lem3982816 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term178 A x s g' t') = (term179 A x s g' t').
Proof. exact (eq_refl (term178 A x s g' t')). Qed.
Lemma lem3982817 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term179 A x s g' t'.
Proof. exact (EQ_MP (@lem3982816 A x s g' t') (@lem3982815 A x s g' t')). Qed.
Lemma lem3982818 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term180 A x s g' t' e'.
Proof. exact (@lem3982817 A x s g' t' e'). Qed.
Lemma lem3982819 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term180 A x s g' t' e') = (term181 A x s g' t' e').
Proof. exact (eq_refl (term180 A x s g' t' e')). Qed.
Lemma lem3982820 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term181 A x s g' t' e'.
Proof. exact (EQ_MP (@lem3982819 A x s g' t' e') (@lem3982818 A x s g' t' e')). Qed.
Lemma lem3982822 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : (@IN A x s) = False.
Proof. exact (@lem3971832 A x s (@lem3971728 A x s h1)). Qed.
Lemma lem3982827 {A : Type'} (x : A) (s : A -> Prop) (t' : nat) (e' : nat) : term182 A x s t' e'.
Proof. exact (@lem3982820 A x s False t' e'). Qed.
Lemma lem3982828 {A : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (h1 : term124 A x s) : term183 A x s t' e'.
Proof. exact (@lem3982827 A x s t' e' (@lem3982822 A x s h1)). Qed.
Lemma lem3982844 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem3982845 {A : Type'} (s : A -> Prop) : term184 A s.
Proof. exact (fun h0 : False => @lem3982844 A s). Qed.
Lemma lem3982846 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term124 A x s) : term185 A x s e'.
Proof. exact (@lem3982828 A (@CARD A s) e' x s h1). Qed.
Lemma lem3982847 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term124 A x s) : term186 A x s e'.
Proof. exact (@lem3982846 A e' x s h1 (@lem3982845 A s)). Qed.
Lemma lem3982873 {A : Type'} (s : A -> Prop) : (term175 A s) = (term175 A s).
Proof. exact (eq_refl (term175 A s)). Qed.
Lemma lem3982874 {A : Type'} (s : A -> Prop) : term187 A s.
Proof. exact (fun h0 : ~ False => @lem3982873 A s). Qed.
Lemma lem3982875 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term188 A x s.
Proof. exact (@lem3982847 A (term175 A s) x s h1). Qed.
Lemma lem3982876 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : (term144 A x s) = (term189 A s).
Proof. exact (@lem3982875 A x s h1 (@lem3982874 A s)). Qed.
Lemma lem3982878 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3982879 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3982878 nat t1 t2). Qed.
Lemma lem3982880 {A : Type'} (s : A -> Prop) : (term189 A s) = (term175 A s).
Proof. exact (@lem3982879 (@CARD A s) (term175 A s)). Qed.
Lemma lem3982901 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : (term144 A x s) = (term175 A s).
Proof. exact (TRANS (@lem3982876 A x s h1) (@lem3982880 A s)). Qed.
Lemma lem3982902 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) : (term115 A x s) = (term175 A s).
Proof. exact (TRANS (@lem3982800 A x s h1) (@lem3982901 A x s h2)). Qed.
Lemma lem3982903 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) : ((term112 A B x f s) = (term115 A x s)) = ((term172 A B x f s) = (term175 A s)).
Proof. exact (MK_COMB (@lem3978435 A B x f s h1) (@lem3982902 A x s h1 h2)). Qed.
Lemma lem3987283 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) : ((term172 A B x f s) = (term175 A s)) = ((term112 A B x f s) = (term115 A x s)).
Proof. exact (SYM (@lem3982903 A B f x s h1 h2)). Qed.
Lemma lem3987284 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term190 _476 _475 _474 _477) = (term191 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem3987285 {A : Type'} (_474 : nat) (_475 : Prop) (s : A -> Prop) (_477 : nat) : (term192 A s _475 _474 _477) = (term193 A _474 _475 s _477).
Proof. exact (@lem3987284 _474 _475 (term194 A s) _477). Qed.
Lemma lem3987286 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term195 A B x f s) = (term196 A B x f s).
Proof. exact (@lem3987285 A (term32 A B f s) (term163 A B x f s) s (term156 A B f s)). Qed.
Lemma lem3987287 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term197 A B f s) = ((term156 A B f s) = (term175 A s)).
Proof. exact (eq_refl (term197 A B f s)). Qed.
Lemma lem3987288 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term198 A B x f s) = (term198 A B x f s).
Proof. exact (eq_refl (term198 A B x f s)). Qed.
Lemma lem3987289 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term199 A B x f s) = (term200 A B x f s).
Proof. exact (MK_COMB (@lem3987288 A B x f s) (@lem3987287 A B f s)). Qed.
Lemma lem3987290 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term201 A B f s) = ((term32 A B f s) = (term175 A s)).
Proof. exact (eq_refl (term201 A B f s)). Qed.
Lemma lem3987291 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term202 A B x f s) = (term202 A B x f s).
Proof. exact (eq_refl (term202 A B x f s)). Qed.
Lemma lem3987292 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term203 A B x f s) = (term204 A B x f s).
Proof. exact (MK_COMB (@lem3987291 A B x f s) (@lem3987290 A B f s)). Qed.
Lemma lem3987293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3987294 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term205 A B x f s) = (term206 A B x f s).
Proof. exact (MK_COMB (@lem3987293) (@lem3987292 A B x f s)). Qed.
Lemma lem3987295 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term196 A B x f s) = (term207 A B x f s).
Proof. exact (MK_COMB (@lem3987294 A B x f s) (@lem3987289 A B x f s)). Qed.
Lemma lem3987296 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term195 A B x f s) = ((term172 A B x f s) = (term175 A s)).
Proof. exact (eq_refl (term195 A B x f s)). Qed.
Lemma lem3987297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3987298 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term208 A B x f s) = (term209 A B x f s).
Proof. exact (MK_COMB (@lem3987297) (@lem3987296 A B x f s)). Qed.
Lemma lem3987299 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term195 A B x f s) = (term196 A B x f s)) = (((term172 A B x f s) = (term175 A s)) = (term207 A B x f s)).
Proof. exact (MK_COMB (@lem3987298 A B x f s) (@lem3987295 A B x f s)). Qed.
Lemma lem3987300 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term172 A B x f s) = (term175 A s)) = (term207 A B x f s).
Proof. exact (EQ_MP (@lem3987299 A B x f s) (@lem3987286 A B x f s)). Qed.
Lemma lem3987301 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term207 A B x f s) = ((term172 A B x f s) = (term175 A s)).
Proof. exact (SYM (@lem3987300 A B x f s)). Qed.
Lemma lem3987302 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term163 A B x f s) : term163 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987319 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term170 A B x f s) : term170 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987337 (p : Prop) : p = (term210 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3987338 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (term175 A s)) = (term211 A B f s).
Proof. exact (@lem3987337 ((term32 A B f s) = (term175 A s))). Qed.
Lemma lem3987339 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term211 A B f s) = ((term32 A B f s) = (term175 A s)).
Proof. exact (SYM (@lem3987338 A B f s)). Qed.
Lemma lem3987340 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term212 A B f s) : term212 A B f s.
Proof. exact (h1). Qed.
Lemma lem3987341 {A : Type'} : term213 A.
Proof. exact (@lem3205665 A). Qed.
Lemma lem3987343 {B : Type'} : term213 B.
Proof. exact (@lem3205665 B). Qed.
Lemma lem3987345 : term214.
Proof. exact (@lem3205665 nat). Qed.
Lemma lem3987348 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term215 A B x f s) : term215 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987349 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term216 A B x f s.
Proof. exact (fun h0 : term215 A B x f s => @lem3987348 A B x f s h0). Qed.
Lemma lem3987350 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term216 A B x f s) : term216 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987351 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term215 A B x f s) : term215 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987352 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term215 A B x f s) (h2 : term216 A B x f s) : term215 A B x f s.
Proof. exact (@lem3987350 A B x f s h2 (@lem3987351 A B x f s h1)). Qed.
Lemma lem3987353 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term215 A B x f s) : term217 A B x f s.
Proof. exact (fun h0 : term216 A B x f s => @lem3987352 A B x f s h1 h0). Qed.
Lemma lem3987354 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term216 A B x f s) : term216 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987355 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term215 A B x f s) (h2 : term216 A B x f s) : term215 A B x f s.
Proof. exact (@lem3987353 A B x f s h1 (@lem3987354 A B x f s h2)). Qed.
Lemma lem3987356 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term216 A B x f s) : term216 A B x f s.
Proof. exact (fun h0 : term215 A B x f s => @lem3987355 A B x f s h0 h1). Qed.
Lemma lem3987357 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term218 A B x f s.
Proof. exact (fun h0 : term216 A B x f s => @lem3987356 A B x f s h0). Qed.
Lemma lem3987360 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term216 A B x f s.
Proof. exact (@lem3987357 A B x f s (@lem3987349 A B x f s)). Qed.
Lemma lem3987361 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term216 A B x f s.
Proof. exact (@lem3987360 A B x f s). Qed.
Lemma lem3987499 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3987500 : term219 = term220.
Proof. exact (@lem3987499 term214). Qed.
Lemma lem3987515 {B : Type'} : (term221 B) = (term221 B).
Proof. exact (eq_refl (term221 B)). Qed.
Lemma lem3987516 {B : Type'} : (term222 B) = (term223 B).
Proof. exact (MK_COMB (@lem3987515 B) (@lem3987500)). Qed.
Lemma lem3987519 {A : Type'} : (term221 A) = (term221 A).
Proof. exact (eq_refl (term221 A)). Qed.
Lemma lem3987520 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem3987519 A) (@lem3987516 B)). Qed.
Lemma lem3987523 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term226 A B f s) = (term226 A B f s).
Proof. exact (eq_refl (term226 A B f s)). Qed.
Lemma lem3987524 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term227 A B f s) = (term228 A B f s).
Proof. exact (MK_COMB (@lem3987523 A B f s) (@lem3987520 A B)). Qed.
Lemma lem3987527 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term202 A B x f s) = (term202 A B x f s).
Proof. exact (eq_refl (term202 A B x f s)). Qed.
Lemma lem3987528 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term229 A B x f s) = (term230 A B x f s).
Proof. exact (MK_COMB (@lem3987527 A B x f s) (@lem3987524 A B f s)). Qed.
Lemma lem3987531 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term116 A B f x s) = (term116 A B f x s).
Proof. exact (eq_refl (term116 A B f x s)). Qed.
Lemma lem3987532 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term231 A B x f s) = (term232 A B x f s).
Proof. exact (MK_COMB (@lem3987531 A B f x s) (@lem3987528 A B x f s)). Qed.
Lemma lem3987535 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3987536 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term233 A B x f s) = (term234 A B x f s).
Proof. exact (MK_COMB (@lem3987535 A s) (@lem3987532 A B x f s)). Qed.
Lemma lem3987539 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem3987540 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term236 A B x f s) = (term237 A B x f s).
Proof. exact (MK_COMB (@lem3987539 A x s) (@lem3987536 A B x f s)). Qed.
Lemma lem3987543 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term238 A B f s) = (term238 A B f s).
Proof. exact (eq_refl (term238 A B f s)). Qed.
Lemma lem3987544 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term215 A B x f s) = (term239 A B x f s).
Proof. exact (MK_COMB (@lem3987543 A B f s) (@lem3987540 A B x f s)). Qed.
Lemma lem3987547 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term240 A B f s) = (term241 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3987544 A B x f s)). Qed.
Lemma lem3987548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987549 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term242 A B f s) = (term243 A B f s).
Proof. exact (MK_COMB (@lem3987548 A) (@lem3987547 A B f s)). Qed.
Lemma lem3987554 {A B : Type'} (s : A -> Prop) : (term244 A B s) = (term245 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3987549 A B f s)). Qed.
Lemma lem3987555 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3987556 {A B : Type'} (s : A -> Prop) : (term246 A B s) = (term247 A B s).
Proof. exact (MK_COMB (@lem3987555 A B) (@lem3987554 A B s)). Qed.
Lemma lem3987561 {A B : Type'} : (term248 A B) = (term249 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3987556 A B s)). Qed.
Lemma lem3987562 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3987571 {A B : Type'} : (term250 A B) = (term251 A B).
Proof. exact (MK_COMB (@lem3987562 A) (@lem3987561 A B)). Qed.
Lemma lem3987580 (y : nat) (x : nat) (s : nat -> Prop) : ((term252 x y s) = (term253 y x s)) = ((term252 x y s) = (term253 y x s)).
Proof. exact (eq_refl ((term252 x y s) = (term253 y x s))). Qed.
Lemma lem3987581 (y : nat) (x : nat) : (term254 y x) = (term254 y x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem3987580 y x s)). Qed.
Lemma lem3987582 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem3987583 (y : nat) (x : nat) : (term255 y x) = (term255 y x).
Proof. exact (MK_COMB (@lem3987582) (@lem3987581 y x)). Qed.
Lemma lem3987584 (x : nat) : (term256 x) = (term256 x).
Proof. exact (fun_ext (fun y : nat => @lem3987583 y x)). Qed.
Lemma lem3987585 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3987586 (x : nat) : (term257 x) = (term257 x).
Proof. exact (MK_COMB (@lem3987585) (@lem3987584 x)). Qed.
Lemma lem3987587 : term258 = term258.
Proof. exact (fun_ext (fun x : nat => @lem3987586 x)). Qed.
Lemma lem3987588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3987589 : term214 = term214.
Proof. exact (MK_COMB (@lem3987588) (@lem3987587)). Qed.
Lemma lem3987590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3987591 : term220 = term220.
Proof. exact (MK_COMB (@lem3987590) (@lem3987589)). Qed.
Lemma lem3987600 {B : Type'} (y : B) (x : B) (s : B -> Prop) : ((term259 B x y s) = (term260 B y x s)) = ((term259 B x y s) = (term260 B y x s)).
Proof. exact (eq_refl ((term259 B x y s) = (term260 B y x s))). Qed.
Lemma lem3987601 {B : Type'} (y : B) (x : B) : (term261 B y x) = (term261 B y x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3987600 B y x s)). Qed.
Lemma lem3987602 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3987603 {B : Type'} (y : B) (x : B) : (term262 B y x) = (term262 B y x).
Proof. exact (MK_COMB (@lem3987602 B) (@lem3987601 B y x)). Qed.
Lemma lem3987604 {B : Type'} (x : B) : (term263 B x) = (term263 B x).
Proof. exact (fun_ext (fun y : B => @lem3987603 B y x)). Qed.
Lemma lem3987605 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3987606 {B : Type'} (x : B) : (term264 B x) = (term264 B x).
Proof. exact (MK_COMB (@lem3987605 B) (@lem3987604 B x)). Qed.
Lemma lem3987607 {B : Type'} : (term265 B) = (term265 B).
Proof. exact (fun_ext (fun x : B => @lem3987606 B x)). Qed.
Lemma lem3987608 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3987609 {B : Type'} : (term213 B) = (term213 B).
Proof. exact (MK_COMB (@lem3987608 B) (@lem3987607 B)). Qed.
Lemma lem3987610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3987611 {B : Type'} : (term221 B) = (term221 B).
Proof. exact (MK_COMB (@lem3987610) (@lem3987609 B)). Qed.
Lemma lem3987612 {B : Type'} : (term223 B) = (term223 B).
Proof. exact (MK_COMB (@lem3987611 B) (@lem3987591)). Qed.
Lemma lem3987621 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term259 A x y s) = (term260 A y x s)) = ((term259 A x y s) = (term260 A y x s)).
Proof. exact (eq_refl ((term259 A x y s) = (term260 A y x s))). Qed.
Lemma lem3987622 {A : Type'} (y : A) (x : A) : (term261 A y x) = (term261 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3987621 A y x s)). Qed.
Lemma lem3987623 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3987624 {A : Type'} (y : A) (x : A) : (term262 A y x) = (term262 A y x).
Proof. exact (MK_COMB (@lem3987623 A) (@lem3987622 A y x)). Qed.
Lemma lem3987625 {A : Type'} (x : A) : (term263 A x) = (term263 A x).
Proof. exact (fun_ext (fun y : A => @lem3987624 A y x)). Qed.
Lemma lem3987626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987627 {A : Type'} (x : A) : (term264 A x) = (term264 A x).
Proof. exact (MK_COMB (@lem3987626 A) (@lem3987625 A x)). Qed.
Lemma lem3987628 {A : Type'} : (term265 A) = (term265 A).
Proof. exact (fun_ext (fun x : A => @lem3987627 A x)). Qed.
Lemma lem3987629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987630 {A : Type'} : (term213 A) = (term213 A).
Proof. exact (MK_COMB (@lem3987629 A) (@lem3987628 A)). Qed.
Lemma lem3987631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3987632 {A : Type'} : (term221 A) = (term221 A).
Proof. exact (MK_COMB (@lem3987631) (@lem3987630 A)). Qed.
Lemma lem3987633 {A B : Type'} : (term225 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem3987632 A) (@lem3987612 B)). Qed.
Lemma lem3987638 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term226 A B f s) = (term226 A B f s).
Proof. exact (eq_refl (term226 A B f s)). Qed.
Lemma lem3987639 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term228 A B f s) = (term228 A B f s).
Proof. exact (MK_COMB (@lem3987638 A B f s) (@lem3987633 A B)). Qed.
Lemma lem3987644 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) : (term266 A B x f x' s) = (term266 A B x f x' s).
Proof. exact (eq_refl (term266 A B x f x' s)). Qed.
Lemma lem3987645 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term267 A B x f s) = (term267 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3987644 A B x f x' s)). Qed.
Lemma lem3987646 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3987647 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term163 A B x f s) = (term163 A B x f s).
Proof. exact (MK_COMB (@lem3987646 A) (@lem3987645 A B x f s)). Qed.
Lemma lem3987648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3987649 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term202 A B x f s) = (term202 A B x f s).
Proof. exact (MK_COMB (@lem3987648) (@lem3987647 A B x f s)). Qed.
Lemma lem3987650 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term230 A B x f s) = (term230 A B x f s).
Proof. exact (MK_COMB (@lem3987649 A B x f s) (@lem3987639 A B f s)). Qed.
Lemma lem3987663 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term268 A B f x s x' y) = (term268 A B f x s x' y).
Proof. exact (eq_refl (term268 A B f x s x' y)). Qed.
Lemma lem3987664 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term269 A B f x s x') = (term269 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3987663 A B f x s x' y)). Qed.
Lemma lem3987665 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987666 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term270 A B f x s x') = (term270 A B f x s x').
Proof. exact (MK_COMB (@lem3987665 A) (@lem3987664 A B f x s x')). Qed.
Lemma lem3987667 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term271 A B f x s) = (term271 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3987666 A B f x s x')). Qed.
Lemma lem3987668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987669 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term125 A B f x s) = (term125 A B f x s).
Proof. exact (MK_COMB (@lem3987668 A) (@lem3987667 A B f x s)). Qed.
Lemma lem3987670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3987671 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term116 A B f x s) = (term116 A B f x s).
Proof. exact (MK_COMB (@lem3987670) (@lem3987669 A B f x s)). Qed.
Lemma lem3987672 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term232 A B x f s) = (term232 A B x f s).
Proof. exact (MK_COMB (@lem3987671 A B f x s) (@lem3987650 A B x f s)). Qed.
Lemma lem3987675 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3987676 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term234 A B x f s) = (term234 A B x f s).
Proof. exact (MK_COMB (@lem3987675 A s) (@lem3987672 A B x f s)). Qed.
Lemma lem3987681 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem3987682 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term237 A B x f s) = (term237 A B x f s).
Proof. exact (MK_COMB (@lem3987681 A x s) (@lem3987676 A B x f s)). Qed.
Lemma lem3987683 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987696 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term36 A B f s x y) = (term36 A B f s x y).
Proof. exact (eq_refl (term36 A B f s x y)). Qed.
Lemma lem3987697 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term39 A B f s x) = (term39 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3987696 A B f s x y)). Qed.
Lemma lem3987698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987699 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term41 A B f s x) = (term41 A B f s x).
Proof. exact (MK_COMB (@lem3987698 A) (@lem3987697 A B f s x)). Qed.
Lemma lem3987700 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term43 A B f s) = (term43 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3987699 A B f s x)). Qed.
Lemma lem3987701 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987702 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term44 A B f s) = (term44 A B f s).
Proof. exact (MK_COMB (@lem3987701 A) (@lem3987700 A B f s)). Qed.
Lemma lem3987703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3987704 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term46 A B f s) = (term46 A B f s).
Proof. exact (MK_COMB (@lem3987703) (@lem3987702 A B f s)). Qed.
Lemma lem3987705 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term48 A B f s).
Proof. exact (MK_COMB (@lem3987704 A B f s) (@lem3987683 A B f s)). Qed.
Lemma lem3987706 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3987707 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term238 A B f s) = (term238 A B f s).
Proof. exact (MK_COMB (@lem3987706) (@lem3987705 A B f s)). Qed.
Lemma lem3987708 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term239 A B x f s) = (term239 A B x f s).
Proof. exact (MK_COMB (@lem3987707 A B f s) (@lem3987682 A B x f s)). Qed.
Lemma lem3987709 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term241 A B f s) = (term241 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3987708 A B x f s)). Qed.
Lemma lem3987710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3987711 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term243 A B f s) = (term243 A B f s).
Proof. exact (MK_COMB (@lem3987710 A) (@lem3987709 A B f s)). Qed.
Lemma lem3987712 {A B : Type'} (s : A -> Prop) : (term245 A B s) = (term245 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3987711 A B f s)). Qed.
Lemma lem3987713 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3987714 {A B : Type'} (s : A -> Prop) : (term247 A B s) = (term247 A B s).
Proof. exact (MK_COMB (@lem3987713 A B) (@lem3987712 A B s)). Qed.
Lemma lem3987715 {A B : Type'} : (term249 A B) = (term249 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3987714 A B s)). Qed.
Lemma lem3987716 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3987717 {A B : Type'} : (term251 A B) = (term251 A B).
Proof. exact (MK_COMB (@lem3987716 A) (@lem3987715 A B)). Qed.
Lemma lem3987860 {A B : Type'} : (term250 A B) = (term251 A B).
Proof. exact (TRANS (@lem3987571 A B) (@lem3987717 A B)). Qed.
Lemma lem3987861 {A B : Type'} : (term251 A B) = (term250 A B).
Proof. exact (SYM (@lem3987860 A B)). Qed.
Lemma lem3987862 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term48 A B f s.
Proof. exact (h1). Qed.
Lemma lem3987865 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term125 A B f x s.
Proof. exact (h1). Qed.
Lemma lem3987866 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term163 A B x f s) : term163 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3987868 {A : Type'} (h1 : term213 A) : term213 A.
Proof. exact (h1). Qed.
Lemma lem3987879 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term272 A s x y) = (term273 A s x y).
Proof. exact (@lem17362 (@IN A x s) (x = y)). Qed.
Lemma lem3987881 {A : Type'} (y : A) (s : A -> Prop) : (term274 A y s) = (term274 A y s).
Proof. exact (eq_refl (term274 A y s)). Qed.
Lemma lem3987882 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term275 A s x y) = (term276 A s x y).
Proof. exact (MK_COMB (@lem3987881 A y s) (@lem3987879 A s x y)). Qed.
Lemma lem3987883 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term277 A s x y) = (term275 A s x y).
Proof. exact (@lem17362 (@IN A y s) (term37 A s x y)). Qed.
Lemma lem3987884 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term277 A s x y) = (term276 A s x y).
Proof. exact (TRANS (@lem3987883 A s x y) (@lem3987882 A s x y)). Qed.
Lemma lem3987886 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term278 A B x f y) = (term278 A B x f y).
Proof. exact (eq_refl (term278 A B x f y)). Qed.
Lemma lem3987887 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term279 A B f s x y) = (term280 A B f s x y).
Proof. exact (MK_COMB (@lem3987886 A B x f y) (@lem3987884 A s x y)). Qed.
Lemma lem3987888 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term281 A B f s x y) = (term279 A B f s x y).
Proof. exact (@lem17362 ((f x) = (f y)) (term282 A s x y)). Qed.
Lemma lem3987889 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term281 A B f s x y) = (term280 A B f s x y).
Proof. exact (TRANS (@lem3987888 A B f s x y) (@lem3987887 A B f s x y)). Qed.
Lemma lem3987890 {A : Type'} (P : A -> Prop) : (term283 A P) = (term284 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3987891 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term285 A B f s x) = (term286 A B f s x).
Proof. exact (@lem3987890 A (term39 A B f s x)). Qed.
Lemma lem3987892 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term287 A B f s x y) = (term36 A B f s x y).
Proof. exact (eq_refl (term287 A B f s x y)). Qed.
Lemma lem3987893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3987894 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term288 A B f s x y) = (term281 A B f s x y).
Proof. exact (MK_COMB (@lem3987893) (@lem3987892 A B f s x y)). Qed.
Lemma lem3987895 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term288 A B f s x y) = (term280 A B f s x y).
Proof. exact (TRANS (@lem3987894 A B f s x y) (@lem3987889 A B f s x y)). Qed.
Lemma lem3987896 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term289 A B f s x) = (term290 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3987895 A B f s x y)). Qed.
Lemma lem3987897 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3987898 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term286 A B f s x) = (term291 A B f s x).
Proof. exact (MK_COMB (@lem3987897 A) (@lem3987896 A B f s x)). Qed.
Lemma lem3987899 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term285 A B f s x) = (term291 A B f s x).
Proof. exact (TRANS (@lem3987891 A B f s x) (@lem3987898 A B f s x)). Qed.
Lemma lem3987900 {A : Type'} (P : A -> Prop) : (term283 A P) = (term284 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3987901 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term292 A B f s) = (term293 A B f s).
Proof. exact (@lem3987900 A (term43 A B f s)). Qed.
Lemma lem3987902 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term294 A B f s x) = (term41 A B f s x).
Proof. exact (eq_refl (term294 A B f s x)). Qed.
Lemma lem3987903 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3987904 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term295 A B f s x) = (term285 A B f s x).
Proof. exact (MK_COMB (@lem3987903) (@lem3987902 A B f s x)). Qed.
Lemma lem3987905 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term295 A B f s x) = (term291 A B f s x).
Proof. exact (TRANS (@lem3987904 A B f s x) (@lem3987899 A B f s x)). Qed.
Lemma lem3987906 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term296 A B f s) = (term297 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3987905 A B f s x)). Qed.
Lemma lem3987907 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3987908 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term293 A B f s) = (term298 A B f s).
Proof. exact (MK_COMB (@lem3987907 A) (@lem3987906 A B f s)). Qed.
Lemma lem3987909 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term292 A B f s) = (term298 A B f s).
Proof. exact (TRANS (@lem3987901 A B f s) (@lem3987908 A B f s)). Qed.
Lemma lem3987910 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3987912 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term299 A B f s) = (term300 A B f s).
Proof. exact (MK_COMB (@lem3987911) (@lem3987909 A B f s)). Qed.
Lemma lem3987913 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term301 A B f s) = (term302 A B f s).
Proof. exact (MK_COMB (@lem3987912 A B f s) (@lem3987910 A B f s)). Qed.
Lemma lem3987914 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term301 A B f s).
Proof. exact (@lem17265 (term44 A B f s) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987915 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term302 A B f s).
Proof. exact (TRANS (@lem3987914 A B f s) (@lem3987913 A B f s)). Qed.
Lemma lem3987970 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3987971 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem3987970 A P Q). Qed.
Lemma lem3987972 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term305 A B f s) = (term306 A B f s).
Proof. exact (@lem3987971 A (term297 A B f s) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987973 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term307 A B f s x) = (term291 A B f s x).
Proof. exact (eq_refl (term307 A B f s x)). Qed.
Lemma lem3987974 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term308 A B f s) = (term297 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3987973 A B f s x)). Qed.
Lemma lem3987975 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3987976 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term309 A B f s) = (term298 A B f s).
Proof. exact (MK_COMB (@lem3987975 A) (@lem3987974 A B f s)). Qed.
Lemma lem3987977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3987978 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term310 A B f s) = (term300 A B f s).
Proof. exact (MK_COMB (@lem3987977) (@lem3987976 A B f s)). Qed.
Lemma lem3987979 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987980 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term305 A B f s) = (term302 A B f s).
Proof. exact (MK_COMB (@lem3987978 A B f s) (@lem3987979 A B f s)). Qed.
Lemma lem3987981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3987982 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term311 A B f s) = (term312 A B f s).
Proof. exact (MK_COMB (@lem3987981) (@lem3987980 A B f s)). Qed.
Lemma lem3987983 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term307 A B f s x) = (term291 A B f s x).
Proof. exact (eq_refl (term307 A B f s x)). Qed.
Lemma lem3987984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3987985 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term313 A B f s x) = (term314 A B f s x).
Proof. exact (MK_COMB (@lem3987984) (@lem3987983 A B f s x)). Qed.
Lemma lem3987986 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987987 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term315 A B x f s) = (term316 A B x f s).
Proof. exact (MK_COMB (@lem3987985 A B f s x) (@lem3987986 A B f s)). Qed.
Lemma lem3987988 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term317 A B f s) = (term318 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3987987 A B x f s)). Qed.
Lemma lem3987989 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3987990 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term306 A B f s) = (term319 A B f s).
Proof. exact (MK_COMB (@lem3987989 A) (@lem3987988 A B f s)). Qed.
Lemma lem3987991 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term305 A B f s) = (term306 A B f s)) = ((term302 A B f s) = (term319 A B f s)).
Proof. exact (MK_COMB (@lem3987982 A B f s) (@lem3987990 A B f s)). Qed.
Lemma lem3987992 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term302 A B f s) = (term319 A B f s).
Proof. exact (EQ_MP (@lem3987991 A B f s) (@lem3987972 A B f s)). Qed.
Lemma lem3987994 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3987995 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem3987994 A P Q). Qed.
Lemma lem3987996 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term320 A B x f s) = (term321 A B x f s).
Proof. exact (@lem3987995 A (term290 A B f s x) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3987997 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term322 A B f s x y) = (term280 A B f s x y).
Proof. exact (eq_refl (term322 A B f s x y)). Qed.
Lemma lem3987998 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term323 A B f s x) = (term290 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3987997 A B f s x y)). Qed.
Lemma lem3987999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3988000 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term324 A B f s x) = (term291 A B f s x).
Proof. exact (MK_COMB (@lem3987999 A) (@lem3987998 A B f s x)). Qed.
Lemma lem3988001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3988002 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term325 A B f s x) = (term314 A B f s x).
Proof. exact (MK_COMB (@lem3988001) (@lem3988000 A B f s x)). Qed.
Lemma lem3988003 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3988004 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term320 A B x f s) = (term316 A B x f s).
Proof. exact (MK_COMB (@lem3988002 A B f s x) (@lem3988003 A B f s)). Qed.
Lemma lem3988005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3988006 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term326 A B x f s) = (term327 A B x f s).
Proof. exact (MK_COMB (@lem3988005) (@lem3988004 A B x f s)). Qed.
Lemma lem3988007 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term322 A B f s x y) = (term280 A B f s x y).
Proof. exact (eq_refl (term322 A B f s x y)). Qed.
Lemma lem3988008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3988009 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term328 A B f s x y) = (term329 A B f s x y).
Proof. exact (MK_COMB (@lem3988008) (@lem3988007 A B f s x y)). Qed.
Lemma lem3988010 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3988011 {A B : Type'} (x : A) (y : A) (f : A -> B) (s : A -> Prop) : (term330 A B x y f s) = (term331 A B x y f s).
Proof. exact (MK_COMB (@lem3988009 A B f s x y) (@lem3988010 A B f s)). Qed.
Lemma lem3988012 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term332 A B x f s) = (term333 A B x f s).
Proof. exact (fun_ext (fun y : A => @lem3988011 A B x y f s)). Qed.
Lemma lem3988013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3988014 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term334 A B x f s).
Proof. exact (MK_COMB (@lem3988013 A) (@lem3988012 A B x f s)). Qed.
Lemma lem3988015 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term320 A B x f s) = (term321 A B x f s)) = ((term316 A B x f s) = (term334 A B x f s)).
Proof. exact (MK_COMB (@lem3988006 A B x f s) (@lem3988014 A B x f s)). Qed.
Lemma lem3988016 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term316 A B x f s) = (term334 A B x f s).
Proof. exact (EQ_MP (@lem3988015 A B x f s) (@lem3987996 A B x f s)). Qed.
Lemma lem3988017 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term318 A B f s) = (term335 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3988016 A B x f s)). Qed.
Lemma lem3988018 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3988019 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term319 A B f s) = (term336 A B f s).
Proof. exact (MK_COMB (@lem3988018 A) (@lem3988017 A B f s)). Qed.
Lemma lem3988021 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term302 A B f s) = (term336 A B f s).
Proof. exact (TRANS (@lem3987992 A B f s) (@lem3988019 A B f s)). Qed.
Lemma lem3988022 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term336 A B f s).
Proof. exact (TRANS (@lem3987915 A B f s) (@lem3988021 A B f s)). Qed.
Lemma lem3988023 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term336 A B f s.
Proof. exact (EQ_MP (@lem3988022 A B f s) (@lem3987862 A B f s h1)). Qed.
Lemma lem3988029 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term124 A x s.
Proof. exact (h1). Qed.
Lemma lem3988044 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term337 A x s x' y) = (term338 A x s x' y).
Proof. exact (@lem17265 (term259 A x' x s) (x' = y)). Qed.
Lemma lem3988046 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term339 A y x s) = (term339 A y x s).
Proof. exact (eq_refl (term339 A y x s)). Qed.
Lemma lem3988047 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term340 A x s x' y) = (term341 A x s x' y).
Proof. exact (MK_COMB (@lem3988046 A y x s) (@lem3988044 A x s x' y)). Qed.
Lemma lem3988048 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term342 A x s x' y) = (term340 A x s x' y).
Proof. exact (@lem17265 (term259 A y x s) (term337 A x s x' y)). Qed.
Lemma lem3988049 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term342 A x s x' y) = (term341 A x s x' y).
Proof. exact (TRANS (@lem3988048 A x s x' y) (@lem3988047 A x s x' y)). Qed.
Lemma lem3988051 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term343 A B x' f y) = (term343 A B x' f y).
Proof. exact (eq_refl (term343 A B x' f y)). Qed.
Lemma lem3988052 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term344 A B f x s x' y) = (term345 A B f x s x' y).
Proof. exact (MK_COMB (@lem3988051 A B x' f y) (@lem3988049 A x s x' y)). Qed.
Lemma lem3988053 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term268 A B f x s x' y) = (term344 A B f x s x' y).
Proof. exact (@lem17265 ((f x') = (f y)) (term342 A x s x' y)). Qed.
Lemma lem3988054 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term268 A B f x s x' y) = (term345 A B f x s x' y).
Proof. exact (TRANS (@lem3988053 A B f x s x' y) (@lem3988052 A B f x s x' y)). Qed.
Lemma lem3988055 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term269 A B f x s x') = (term346 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3988054 A B f x s x' y)). Qed.
Lemma lem3988056 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988057 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term270 A B f x s x') = (term347 A B f x s x').
Proof. exact (MK_COMB (@lem3988056 A) (@lem3988055 A B f x s x')). Qed.
Lemma lem3988058 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term271 A B f x s) = (term348 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3988057 A B f x s x')). Qed.
Lemma lem3988059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988116 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term125 A B f x s) = (term349 A B f x s).
Proof. exact (MK_COMB (@lem3988059 A) (@lem3988058 A B f x s)). Qed.
Lemma lem3988117 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term349 A B f x s.
Proof. exact (EQ_MP (@lem3988116 A B f x s) (@lem3987865 A B f x s h1)). Qed.
Lemma lem3988122 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) : (term266 A B x f x' s) = (term266 A B x f x' s).
Proof. exact (eq_refl (term266 A B x f x' s)). Qed.
Lemma lem3988123 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term267 A B x f s) = (term267 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3988122 A B x f x' s)). Qed.
Lemma lem3988124 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3988177 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term163 A B x f s) = (term163 A B x f s).
Proof. exact (MK_COMB (@lem3988124 A) (@lem3988123 A B x f s)). Qed.
Lemma lem3988178 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term163 A B x f s) : term163 A B x f s.
Proof. exact (EQ_MP (@lem3988177 A B x f s) (@lem3987866 A B x f s h1)). Qed.
Lemma lem3988195 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term350 A y x s) = (term351 A y x s).
Proof. exact (@lem17160 (x = y) (@IN A x s)). Qed.
Lemma lem3988201 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term352 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term352 A y x s)). Qed.
Lemma lem3988203 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term353 A x y s) = (term353 A x y s).
Proof. exact (eq_refl (term353 A x y s)). Qed.
Lemma lem3988204 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term354 A y x s) = (term355 A y x s).
Proof. exact (MK_COMB (@lem3988203 A x y s) (@lem3988195 A y x s)). Qed.
Lemma lem3988205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988206 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term356 A y x s) = (term357 A y x s).
Proof. exact (MK_COMB (@lem3988205) (@lem3988204 A y x s)). Qed.
Lemma lem3988207 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term358 A y x s) = (term359 A y x s).
Proof. exact (MK_COMB (@lem3988206 A y x s) (@lem3988201 A y x s)). Qed.
Lemma lem3988208 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term259 A x y s) = (term260 A y x s)) = (term358 A y x s).
Proof. exact (@lem17784 (term259 A x y s) (term260 A y x s)). Qed.
Lemma lem3988209 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term259 A x y s) = (term260 A y x s)) = (term359 A y x s).
Proof. exact (TRANS (@lem3988208 A y x s) (@lem3988207 A y x s)). Qed.
Lemma lem3988210 {A : Type'} (y : A) (x : A) : (term261 A y x) = (term360 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3988209 A y x s)). Qed.
Lemma lem3988211 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3988212 {A : Type'} (y : A) (x : A) : (term262 A y x) = (term361 A y x).
Proof. exact (MK_COMB (@lem3988211 A) (@lem3988210 A y x)). Qed.
Lemma lem3988213 {A : Type'} (x : A) : (term263 A x) = (term362 A x).
Proof. exact (fun_ext (fun y : A => @lem3988212 A y x)). Qed.
Lemma lem3988214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988215 {A : Type'} (x : A) : (term264 A x) = (term363 A x).
Proof. exact (MK_COMB (@lem3988214 A) (@lem3988213 A x)). Qed.
Lemma lem3988216 {A : Type'} : (term265 A) = (term364 A).
Proof. exact (fun_ext (fun x : A => @lem3988215 A x)). Qed.
Lemma lem3988217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988218 {A : Type'} : (term213 A) = (term365 A).
Proof. exact (MK_COMB (@lem3988217 A) (@lem3988216 A)). Qed.
Lemma lem3988228 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3988229 {A : Type'} (P : type686 A) (Q : type686 A) : (term368 A P Q) = (term369 A P Q).
Proof. exact (@lem3988228 (A -> Prop) P Q). Qed.
Lemma lem3988230 {A : Type'} (y : A) (x : A) : (term370 A y x) = (term371 A y x).
Proof. exact (@lem3988229 A (term372 A y x) (term373 A y x)). Qed.
Lemma lem3988231 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term374 A y x s) = (term355 A y x s).
Proof. exact (eq_refl (term374 A y x s)). Qed.
Lemma lem3988232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988233 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term375 A y x s) = (term357 A y x s).
Proof. exact (MK_COMB (@lem3988232) (@lem3988231 A y x s)). Qed.
Lemma lem3988234 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term376 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term376 A y x s)). Qed.
Lemma lem3988235 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term377 A y x s) = (term359 A y x s).
Proof. exact (MK_COMB (@lem3988233 A y x s) (@lem3988234 A y x s)). Qed.
Lemma lem3988236 {A : Type'} (y : A) (x : A) : (term378 A y x) = (term360 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3988235 A y x s)). Qed.
Lemma lem3988237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3988238 {A : Type'} (y : A) (x : A) : (term370 A y x) = (term361 A y x).
Proof. exact (MK_COMB (@lem3988237 A) (@lem3988236 A y x)). Qed.
Lemma lem3988239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3988240 {A : Type'} (y : A) (x : A) : (term379 A y x) = (term380 A y x).
Proof. exact (MK_COMB (@lem3988239) (@lem3988238 A y x)). Qed.
Lemma lem3988241 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term374 A y x s) = (term355 A y x s).
Proof. exact (eq_refl (term374 A y x s)). Qed.
Lemma lem3988242 {A : Type'} (y : A) (x : A) : (term381 A y x) = (term372 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3988241 A y x s)). Qed.
Lemma lem3988243 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3988244 {A : Type'} (y : A) (x : A) : (term382 A y x) = (term383 A y x).
Proof. exact (MK_COMB (@lem3988243 A) (@lem3988242 A y x)). Qed.
Lemma lem3988245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988246 {A : Type'} (y : A) (x : A) : (term384 A y x) = (term385 A y x).
Proof. exact (MK_COMB (@lem3988245) (@lem3988244 A y x)). Qed.
Lemma lem3988247 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term376 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term376 A y x s)). Qed.
Lemma lem3988248 {A : Type'} (y : A) (x : A) : (term386 A y x) = (term373 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3988247 A y x s)). Qed.
Lemma lem3988249 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3988250 {A : Type'} (y : A) (x : A) : (term387 A y x) = (term388 A y x).
Proof. exact (MK_COMB (@lem3988249 A) (@lem3988248 A y x)). Qed.
Lemma lem3988251 {A : Type'} (y : A) (x : A) : (term371 A y x) = (term389 A y x).
Proof. exact (MK_COMB (@lem3988246 A y x) (@lem3988250 A y x)). Qed.
Lemma lem3988252 {A : Type'} (y : A) (x : A) : ((term370 A y x) = (term371 A y x)) = ((term361 A y x) = (term389 A y x)).
Proof. exact (MK_COMB (@lem3988240 A y x) (@lem3988251 A y x)). Qed.
Lemma lem3988253 {A : Type'} (y : A) (x : A) : (term361 A y x) = (term389 A y x).
Proof. exact (EQ_MP (@lem3988252 A y x) (@lem3988230 A y x)). Qed.
Lemma lem3988350 {A : Type'} (x : A) : (term362 A x) = (term390 A x).
Proof. exact (fun_ext (fun y : A => @lem3988253 A y x)). Qed.
Lemma lem3988351 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988352 {A : Type'} (x : A) : (term363 A x) = (term391 A x).
Proof. exact (MK_COMB (@lem3988351 A) (@lem3988350 A x)). Qed.
Lemma lem3988354 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3988355 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (@lem3988354 A P Q). Qed.
Lemma lem3988356 {A : Type'} (x : A) : (term392 A x) = (term393 A x).
Proof. exact (@lem3988355 A (term394 A x) (term395 A x)). Qed.
Lemma lem3988357 {A : Type'} (y : A) (x : A) : (term396 A x y) = (term383 A y x).
Proof. exact (eq_refl (term396 A x y)). Qed.
Lemma lem3988358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988359 {A : Type'} (y : A) (x : A) : (term397 A x y) = (term385 A y x).
Proof. exact (MK_COMB (@lem3988358) (@lem3988357 A y x)). Qed.
Lemma lem3988360 {A : Type'} (y : A) (x : A) : (term398 A x y) = (term388 A y x).
Proof. exact (eq_refl (term398 A x y)). Qed.
Lemma lem3988361 {A : Type'} (y : A) (x : A) : (term399 A x y) = (term389 A y x).
Proof. exact (MK_COMB (@lem3988359 A y x) (@lem3988360 A y x)). Qed.
Lemma lem3988362 {A : Type'} (x : A) : (term400 A x) = (term390 A x).
Proof. exact (fun_ext (fun y : A => @lem3988361 A y x)). Qed.
Lemma lem3988363 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988364 {A : Type'} (x : A) : (term392 A x) = (term391 A x).
Proof. exact (MK_COMB (@lem3988363 A) (@lem3988362 A x)). Qed.
Lemma lem3988365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3988366 {A : Type'} (x : A) : (term401 A x) = (term402 A x).
Proof. exact (MK_COMB (@lem3988365) (@lem3988364 A x)). Qed.
Lemma lem3988367 {A : Type'} (y : A) (x : A) : (term396 A x y) = (term383 A y x).
Proof. exact (eq_refl (term396 A x y)). Qed.
Lemma lem3988368 {A : Type'} (x : A) : (term403 A x) = (term394 A x).
Proof. exact (fun_ext (fun y : A => @lem3988367 A y x)). Qed.
Lemma lem3988369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988370 {A : Type'} (x : A) : (term404 A x) = (term405 A x).
Proof. exact (MK_COMB (@lem3988369 A) (@lem3988368 A x)). Qed.
Lemma lem3988371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988372 {A : Type'} (x : A) : (term406 A x) = (term407 A x).
Proof. exact (MK_COMB (@lem3988371) (@lem3988370 A x)). Qed.
Lemma lem3988373 {A : Type'} (y : A) (x : A) : (term398 A x y) = (term388 A y x).
Proof. exact (eq_refl (term398 A x y)). Qed.
Lemma lem3988374 {A : Type'} (x : A) : (term408 A x) = (term395 A x).
Proof. exact (fun_ext (fun y : A => @lem3988373 A y x)). Qed.
Lemma lem3988375 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988376 {A : Type'} (x : A) : (term409 A x) = (term410 A x).
Proof. exact (MK_COMB (@lem3988375 A) (@lem3988374 A x)). Qed.
Lemma lem3988377 {A : Type'} (x : A) : (term393 A x) = (term411 A x).
Proof. exact (MK_COMB (@lem3988372 A x) (@lem3988376 A x)). Qed.
Lemma lem3988378 {A : Type'} (x : A) : ((term392 A x) = (term393 A x)) = ((term391 A x) = (term411 A x)).
Proof. exact (MK_COMB (@lem3988366 A x) (@lem3988377 A x)). Qed.
Lemma lem3988379 {A : Type'} (x : A) : (term391 A x) = (term411 A x).
Proof. exact (EQ_MP (@lem3988378 A x) (@lem3988356 A x)). Qed.
Lemma lem3988484 {A : Type'} (x : A) : (term363 A x) = (term411 A x).
Proof. exact (TRANS (@lem3988352 A x) (@lem3988379 A x)). Qed.
Lemma lem3988485 {A : Type'} : (term364 A) = (term412 A).
Proof. exact (fun_ext (fun x : A => @lem3988484 A x)). Qed.
Lemma lem3988486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988487 {A : Type'} : (term365 A) = (term413 A).
Proof. exact (MK_COMB (@lem3988486 A) (@lem3988485 A)). Qed.
Lemma lem3988489 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3988490 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (@lem3988489 A P Q). Qed.
Lemma lem3988491 {A : Type'} : (term414 A) = (term415 A).
Proof. exact (@lem3988490 A (term416 A) (term417 A)). Qed.
Lemma lem3988492 {A : Type'} (x : A) : (term418 A x) = (term405 A x).
Proof. exact (eq_refl (term418 A x)). Qed.
Lemma lem3988493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988494 {A : Type'} (x : A) : (term419 A x) = (term407 A x).
Proof. exact (MK_COMB (@lem3988493) (@lem3988492 A x)). Qed.
Lemma lem3988495 {A : Type'} (x : A) : (term420 A x) = (term410 A x).
Proof. exact (eq_refl (term420 A x)). Qed.
Lemma lem3988496 {A : Type'} (x : A) : (term421 A x) = (term411 A x).
Proof. exact (MK_COMB (@lem3988494 A x) (@lem3988495 A x)). Qed.
Lemma lem3988497 {A : Type'} : (term422 A) = (term412 A).
Proof. exact (fun_ext (fun x : A => @lem3988496 A x)). Qed.
Lemma lem3988498 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988499 {A : Type'} : (term414 A) = (term413 A).
Proof. exact (MK_COMB (@lem3988498 A) (@lem3988497 A)). Qed.
Lemma lem3988500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3988501 {A : Type'} : (term423 A) = (term424 A).
Proof. exact (MK_COMB (@lem3988500) (@lem3988499 A)). Qed.
Lemma lem3988502 {A : Type'} (x : A) : (term418 A x) = (term405 A x).
Proof. exact (eq_refl (term418 A x)). Qed.
Lemma lem3988503 {A : Type'} : (term425 A) = (term416 A).
Proof. exact (fun_ext (fun x : A => @lem3988502 A x)). Qed.
Lemma lem3988504 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988505 {A : Type'} : (term426 A) = (term427 A).
Proof. exact (MK_COMB (@lem3988504 A) (@lem3988503 A)). Qed.
Lemma lem3988506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3988507 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (MK_COMB (@lem3988506) (@lem3988505 A)). Qed.
Lemma lem3988508 {A : Type'} (x : A) : (term420 A x) = (term410 A x).
Proof. exact (eq_refl (term420 A x)). Qed.
Lemma lem3988509 {A : Type'} : (term430 A) = (term417 A).
Proof. exact (fun_ext (fun x : A => @lem3988508 A x)). Qed.
Lemma lem3988510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3988511 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (MK_COMB (@lem3988510 A) (@lem3988509 A)). Qed.
Lemma lem3988512 {A : Type'} : (term415 A) = (term433 A).
Proof. exact (MK_COMB (@lem3988507 A) (@lem3988511 A)). Qed.
Lemma lem3988513 {A : Type'} : ((term414 A) = (term415 A)) = ((term413 A) = (term433 A)).
Proof. exact (MK_COMB (@lem3988501 A) (@lem3988512 A)). Qed.
Lemma lem3988514 {A : Type'} : (term413 A) = (term433 A).
Proof. exact (EQ_MP (@lem3988513 A) (@lem3988491 A)). Qed.
Lemma lem3988629 {A : Type'} : (term365 A) = (term433 A).
Proof. exact (TRANS (@lem3988487 A) (@lem3988514 A)). Qed.
Lemma lem3988630 {A : Type'} : (term213 A) = (term433 A).
Proof. exact (TRANS (@lem3988218 A) (@lem3988629 A)). Qed.
Lemma lem3988631 {A : Type'} (h1 : term213 A) : term433 A.
Proof. exact (EQ_MP (@lem3988630 A) (@lem3987868 A h1)). Qed.
Lemma lem3989526 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : term266 A B x f x' s.
Proof. exact (h1). Qed.
Lemma lem3989527 {A B : Type'} (x'' : A) (f : A -> B) (s : A -> Prop) (h1 : term334 A B x'' f s) : term334 A B x'' f s.
Proof. exact (h1). Qed.
Lemma lem3989528 {A B : Type'} (x'' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term331 A B x'' y f s) : term331 A B x'' y f s.
Proof. exact (h1). Qed.
Lemma lem3989536 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term124 A x s.
Proof. exact (h1). Qed.
Lemma lem3989573 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term341 A x s x' y) = (term341 A x s x' y).
Proof. exact (eq_refl (term341 A x s x' y)). Qed.
Lemma lem3989574 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3989575 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3989580 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3989581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3989580 A B f x). Qed.
Lemma lem3989583 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem3989581 A B f x'). Qed.
Lemma lem3989588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3989589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3989588 A B f x). Qed.
Lemma lem3989591 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3989589 A B f y). Qed.
Lemma lem3989592 {A B : Type'} (f : A -> B) (x' : A) : (term434 A B f x') = (term435 A B f x').
Proof. exact (MK_COMB (@lem3989575 B) (@lem3989583 A B f x')). Qed.
Lemma lem3989593 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3989592 A B f x') (@lem3989591 A B f y)). Qed.
Lemma lem3989594 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term436 A B x' f y) = (term437 A B x' f y).
Proof. exact (MK_COMB (@lem3989574) (@lem3989593 A B x' f y)). Qed.
Lemma lem3989595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3989596 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term343 A B x' f y) = (term438 A B x' f y).
Proof. exact (MK_COMB (@lem3989595) (@lem3989594 A B x' f y)). Qed.
Lemma lem3989597 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term345 A B f x s x' y) = (term439 A B f x s x' y).
Proof. exact (MK_COMB (@lem3989596 A B x' f y) (@lem3989573 A x s x' y)). Qed.
Lemma lem3989598 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term346 A B f x s x') = (term440 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3989597 A B f x s x' y)). Qed.
Lemma lem3989599 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989600 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term347 A B f x s x') = (term441 A B f x s x').
Proof. exact (MK_COMB (@lem3989599 A) (@lem3989598 A B f x s x')). Qed.
Lemma lem3989601 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term348 A B f x s) = (term442 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3989600 A B f x s x')). Qed.
Lemma lem3989602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989603 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term349 A B f x s) = (term443 A B f x s).
Proof. exact (MK_COMB (@lem3989602 A) (@lem3989601 A B f x s)). Qed.
Lemma lem3989604 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term443 A B f x s.
Proof. exact (EQ_MP (@lem3989603 A B f x s) (@lem3988117 A B f x s h1)). Qed.
Lemma lem3989649 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term352 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term352 A y x s)). Qed.
Lemma lem3989650 {A : Type'} (y : A) (x : A) : (term373 A y x) = (term373 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3989649 A y x s)). Qed.
Lemma lem3989651 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3989652 {A : Type'} (y : A) (x : A) : (term388 A y x) = (term388 A y x).
Proof. exact (MK_COMB (@lem3989651 A) (@lem3989650 A y x)). Qed.
Lemma lem3989653 {A : Type'} (x : A) : (term395 A x) = (term395 A x).
Proof. exact (fun_ext (fun y : A => @lem3989652 A y x)). Qed.
Lemma lem3989654 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989655 {A : Type'} (x : A) : (term410 A x) = (term410 A x).
Proof. exact (MK_COMB (@lem3989654 A) (@lem3989653 A x)). Qed.
Lemma lem3989656 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (fun_ext (fun x : A => @lem3989655 A x)). Qed.
Lemma lem3989657 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989658 {A : Type'} : (term432 A) = (term432 A).
Proof. exact (MK_COMB (@lem3989657 A) (@lem3989656 A)). Qed.
Lemma lem3989687 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term355 A y x s) = (term355 A y x s).
Proof. exact (eq_refl (term355 A y x s)). Qed.
Lemma lem3989688 {A : Type'} (y : A) (x : A) : (term372 A y x) = (term372 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3989687 A y x s)). Qed.
Lemma lem3989689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3989690 {A : Type'} (y : A) (x : A) : (term383 A y x) = (term383 A y x).
Proof. exact (MK_COMB (@lem3989689 A) (@lem3989688 A y x)). Qed.
Lemma lem3989691 {A : Type'} (x : A) : (term394 A x) = (term394 A x).
Proof. exact (fun_ext (fun y : A => @lem3989690 A y x)). Qed.
Lemma lem3989692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989693 {A : Type'} (x : A) : (term405 A x) = (term405 A x).
Proof. exact (MK_COMB (@lem3989692 A) (@lem3989691 A x)). Qed.
Lemma lem3989694 {A : Type'} : (term416 A) = (term416 A).
Proof. exact (fun_ext (fun x : A => @lem3989693 A x)). Qed.
Lemma lem3989695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989696 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem3989695 A) (@lem3989694 A)). Qed.
Lemma lem3989697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3989698 {A : Type'} : (term429 A) = (term429 A).
Proof. exact (MK_COMB (@lem3989697) (@lem3989696 A)). Qed.
Lemma lem3989699 {A : Type'} : (term433 A) = (term433 A).
Proof. exact (MK_COMB (@lem3989698 A) (@lem3989658 A)). Qed.
Lemma lem3989700 {A : Type'} (h1 : term213 A) : term433 A.
Proof. exact (EQ_MP (@lem3989699 A) (@lem3988631 A h1)). Qed.
Lemma lem3989861 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem3989862 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3989867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3989869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3989867 A B f x). Qed.
Lemma lem3989874 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3989875 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3989874 A B f x). Qed.
Lemma lem3989877 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem3989875 A B f x'). Qed.
Lemma lem3989878 {A B : Type'} (f : A -> B) (x : A) : (term434 A B f x) = (term435 A B f x).
Proof. exact (MK_COMB (@lem3989862 B) (@lem3989869 A B f x)). Qed.
Lemma lem3989879 {A B : Type'} (x : A) (f : A -> B) (x' : A) : ((f x) = (f x')) = ((@I (A -> B) f x) = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem3989878 A B f x) (@lem3989877 A B f x')). Qed.
Lemma lem3989880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3989881 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term278 A B x f x') = (term444 A B x f x').
Proof. exact (MK_COMB (@lem3989880) (@lem3989879 A B x f x')). Qed.
Lemma lem3989882 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) : (term266 A B x f x' s) = (term445 A B x f x' s).
Proof. exact (MK_COMB (@lem3989881 A B x f x') (@lem3989861 A x' s)). Qed.
Lemma lem3989883 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : term445 A B x f x' s.
Proof. exact (EQ_MP (@lem3989882 A B x f x' s) (@lem3989526 A B x f x' s h1)). Qed.
Lemma lem3989896 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3989919 {A : Type'} (s : A -> Prop) (x'' : A) (y : A) : (term276 A s x'' y) = (term276 A s x'' y).
Proof. exact (eq_refl (term276 A s x'' y)). Qed.
Lemma lem3989920 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3989925 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3989926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3989925 A B f x). Qed.
Lemma lem3989928 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (@I (A -> B) f x'').
Proof. exact (@lem3989926 A B f x''). Qed.
Lemma lem3989933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3989934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3989933 A B f x). Qed.
Lemma lem3989936 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3989934 A B f y). Qed.
Lemma lem3989937 {A B : Type'} (f : A -> B) (x'' : A) : (term434 A B f x'') = (term435 A B f x'').
Proof. exact (MK_COMB (@lem3989920 B) (@lem3989928 A B f x'')). Qed.
Lemma lem3989938 {A B : Type'} (x'' : A) (f : A -> B) (y : A) : ((f x'') = (f y)) = ((@I (A -> B) f x'') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3989937 A B f x'') (@lem3989936 A B f y)). Qed.
Lemma lem3989939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3989940 {A B : Type'} (x'' : A) (f : A -> B) (y : A) : (term278 A B x'' f y) = (term444 A B x'' f y).
Proof. exact (MK_COMB (@lem3989939) (@lem3989938 A B x'' f y)). Qed.
Lemma lem3989941 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) : (term280 A B f s x'' y) = (term446 A B f s x'' y).
Proof. exact (MK_COMB (@lem3989940 A B x'' f y) (@lem3989919 A s x'' y)). Qed.
Lemma lem3989942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3989943 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) : (term329 A B f s x'' y) = (term447 A B f s x'' y).
Proof. exact (MK_COMB (@lem3989942) (@lem3989941 A B f s x'' y)). Qed.
Lemma lem3989944 {A B : Type'} (x'' : A) (y : A) (f : A -> B) (s : A -> Prop) : (term331 A B x'' y f s) = (term448 A B x'' y f s).
Proof. exact (MK_COMB (@lem3989943 A B f s x'' y) (@lem3989896 A B f s)). Qed.
Lemma lem3989945 {A B : Type'} (x'' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term331 A B x'' y f s) : term448 A B x'' y f s.
Proof. exact (EQ_MP (@lem3989944 A B x'' y f s) (@lem3989528 A B x'' y f s h1)). Qed.
Lemma lem3989953 {A : Type'} (h1 : term213 A) : term427 A.
Proof. exact (proj1 (@lem3989700 A h1)). Qed.
Lemma lem3989954 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term446 A B f s x'' y.
Proof. exact (h1). Qed.
Lemma lem3989956 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term276 A s x'' y.
Proof. exact (proj2 (@lem3989954 A B f s x'' y h1)). Qed.
Lemma lem3989958 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term273 A s x'' y.
Proof. exact (proj2 (@lem3989956 A B f s x'' y h1)). Qed.
Lemma lem3989989 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term439 A B f x s x' y) = (term439 A B f x s x' y).
Proof. exact (eq_refl (term439 A B f x s x' y)). Qed.
Lemma lem3989990 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term440 A B f x s x') = (term440 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3989989 A B f x s x' y)). Qed.
Lemma lem3989991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989992 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term441 A B f x s x') = (term441 A B f x s x').
Proof. exact (MK_COMB (@lem3989991 A) (@lem3989990 A B f x s x')). Qed.
Lemma lem3989993 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term442 A B f x s) = (term442 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3989992 A B f x s x')). Qed.
Lemma lem3989994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3989996 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term443 A B f x s) = (term443 A B f x s).
Proof. exact (MK_COMB (@lem3989994 A) (@lem3989993 A B f x s)). Qed.
Lemma lem3989997 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term443 A B f x s.
Proof. exact (EQ_MP (@lem3989996 A B f x s) (@lem3989604 A B f x s h1)). Qed.
Lemma lem3990135 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term355 A y x s) = (term449 A y x s).
Proof. exact (@lem19490 (term450 A x y) (term259 A x y s) (term124 A x s)). Qed.
Lemma lem3990136 {A : Type'} (y : A) (x : A) : (term372 A y x) = (term451 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3990135 A y x s)). Qed.
Lemma lem3990137 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3990138 {A : Type'} (y : A) (x : A) : (term383 A y x) = (term452 A y x).
Proof. exact (MK_COMB (@lem3990137 A) (@lem3990136 A y x)). Qed.
Lemma lem3990139 {A : Type'} (x : A) : (term394 A x) = (term453 A x).
Proof. exact (fun_ext (fun y : A => @lem3990138 A y x)). Qed.
Lemma lem3990140 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3990141 {A : Type'} (x : A) : (term405 A x) = (term454 A x).
Proof. exact (MK_COMB (@lem3990140 A) (@lem3990139 A x)). Qed.
Lemma lem3990142 {A : Type'} : (term416 A) = (term455 A).
Proof. exact (fun_ext (fun x : A => @lem3990141 A x)). Qed.
Lemma lem3990143 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3990145 {A : Type'} : (term427 A) = (term456 A).
Proof. exact (MK_COMB (@lem3990143 A) (@lem3990142 A)). Qed.
Lemma lem3990146 {A : Type'} (h1 : term213 A) : term456 A.
Proof. exact (EQ_MP (@lem3990145 A) (@lem3989953 A h1)). Qed.
Lemma lem3990191 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term124 A x s.
Proof. exact (h1). Qed.
Lemma lem3990215 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term439 A B f x s x' y) = (term439 A B f x s x' y).
Proof. exact (eq_refl (term439 A B f x s x' y)). Qed.
Lemma lem3990216 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term440 A B f x s x') = (term440 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3990215 A B f x s x' y)). Qed.
Lemma lem3990217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3990218 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term441 A B f x s x') = (term441 A B f x s x').
Proof. exact (MK_COMB (@lem3990217 A) (@lem3990216 A B f x s x')). Qed.
Lemma lem3990219 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term442 A B f x s) = (term442 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3990218 A B f x s x')). Qed.
Lemma lem3990220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3990222 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term443 A B f x s) = (term443 A B f x s).
Proof. exact (MK_COMB (@lem3990220 A) (@lem3990219 A B f x s)). Qed.
Lemma lem3990223 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term443 A B f x s.
Proof. exact (EQ_MP (@lem3990222 A B f x s) (@lem3989604 A B f x s h1)). Qed.
Lemma lem3990361 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term355 A y x s) = (term449 A y x s).
Proof. exact (@lem19490 (term450 A x y) (term259 A x y s) (term124 A x s)). Qed.
Lemma lem3990362 {A : Type'} (y : A) (x : A) : (term372 A y x) = (term451 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3990361 A y x s)). Qed.
Lemma lem3990363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3990364 {A : Type'} (y : A) (x : A) : (term383 A y x) = (term452 A y x).
Proof. exact (MK_COMB (@lem3990363 A) (@lem3990362 A y x)). Qed.
Lemma lem3990365 {A : Type'} (x : A) : (term394 A x) = (term453 A x).
Proof. exact (fun_ext (fun y : A => @lem3990364 A y x)). Qed.
Lemma lem3990366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3990367 {A : Type'} (x : A) : (term405 A x) = (term454 A x).
Proof. exact (MK_COMB (@lem3990366 A) (@lem3990365 A x)). Qed.
Lemma lem3990368 {A : Type'} : (term416 A) = (term455 A).
Proof. exact (fun_ext (fun x : A => @lem3990367 A x)). Qed.
Lemma lem3990369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3990371 {A : Type'} : (term427 A) = (term456 A).
Proof. exact (MK_COMB (@lem3990369 A) (@lem3990368 A)). Qed.
Lemma lem3990372 {A : Type'} (h1 : term213 A) : term456 A.
Proof. exact (EQ_MP (@lem3990371 A) (@lem3989953 A h1)). Qed.
Lemma lem3990402 {A B : Type'} (_45830 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term457 A B f x s _45830.
Proof. exact (@lem3989997 A B f x s h1 _45830). Qed.
Lemma lem3990403 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45830 : A) : (term457 A B f x s _45830) = (term441 A B f x s _45830).
Proof. exact (eq_refl (term457 A B f x s _45830)). Qed.
Lemma lem3990404 {A B : Type'} (_45830 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term441 A B f x s _45830.
Proof. exact (EQ_MP (@lem3990403 A B f x s _45830) (@lem3990402 A B _45830 f x s h1)). Qed.
Lemma lem3990405 {A B : Type'} (_45830 : A) (_45831 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term458 A B f x s _45830 _45831.
Proof. exact (@lem3990404 A B _45830 f x s h1 _45831). Qed.
Lemma lem3990406 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45830 : A) (_45831 : A) : (term458 A B f x s _45830 _45831) = (term439 A B f x s _45830 _45831).
Proof. exact (eq_refl (term458 A B f x s _45830 _45831)). Qed.
Lemma lem3990444 {A : Type'} (_45844 : A) (h1 : term213 A) : term459 A _45844.
Proof. exact (@lem3990146 A h1 _45844). Qed.
Lemma lem3990445 {A : Type'} (_45844 : A) : (term459 A _45844) = (term454 A _45844).
Proof. exact (eq_refl (term459 A _45844)). Qed.
Lemma lem3990446 {A : Type'} (_45844 : A) (h1 : term213 A) : term454 A _45844.
Proof. exact (EQ_MP (@lem3990445 A _45844) (@lem3990444 A _45844 h1)). Qed.
Lemma lem3990447 {A : Type'} (_45844 : A) (_45845 : A) (h1 : term213 A) : term460 A _45844 _45845.
Proof. exact (@lem3990446 A _45844 h1 _45845). Qed.
Lemma lem3990448 {A : Type'} (_45845 : A) (_45844 : A) : (term460 A _45844 _45845) = (term452 A _45845 _45844).
Proof. exact (eq_refl (term460 A _45844 _45845)). Qed.
Lemma lem3990449 {A : Type'} (_45845 : A) (_45844 : A) (h1 : term213 A) : term452 A _45845 _45844.
Proof. exact (EQ_MP (@lem3990448 A _45845 _45844) (@lem3990447 A _45844 _45845 h1)). Qed.
Lemma lem3990450 {A : Type'} (_45845 : A) (_45844 : A) (_45846 : A -> Prop) (h1 : term213 A) : term461 A _45845 _45844 _45846.
Proof. exact (@lem3990449 A _45845 _45844 h1 _45846). Qed.
Lemma lem3990451 {A : Type'} (_45845 : A) (_45844 : A) (_45846 : A -> Prop) : (term461 A _45845 _45844 _45846) = (term449 A _45845 _45844 _45846).
Proof. exact (eq_refl (term461 A _45845 _45844 _45846)). Qed.
Lemma lem3990452 {A : Type'} (_45845 : A) (_45844 : A) (_45846 : A -> Prop) (h1 : term213 A) : term449 A _45845 _45844 _45846.
Proof. exact (EQ_MP (@lem3990451 A _45845 _45844 _45846) (@lem3990450 A _45845 _45844 _45846 h1)). Qed.
Lemma lem3990462 {A B : Type'} (_45850 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term457 A B f x s _45850.
Proof. exact (@lem3990223 A B f x s h1 _45850). Qed.
Lemma lem3990463 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45850 : A) : (term457 A B f x s _45850) = (term441 A B f x s _45850).
Proof. exact (eq_refl (term457 A B f x s _45850)). Qed.
Lemma lem3990464 {A B : Type'} (_45850 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term441 A B f x s _45850.
Proof. exact (EQ_MP (@lem3990463 A B f x s _45850) (@lem3990462 A B _45850 f x s h1)). Qed.
Lemma lem3990465 {A B : Type'} (_45850 : A) (_45851 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term458 A B f x s _45850 _45851.
Proof. exact (@lem3990464 A B _45850 f x s h1 _45851). Qed.
Lemma lem3990466 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45850 : A) (_45851 : A) : (term458 A B f x s _45850 _45851) = (term439 A B f x s _45850 _45851).
Proof. exact (eq_refl (term458 A B f x s _45850 _45851)). Qed.
Lemma lem3990504 {A : Type'} (_45864 : A) (h1 : term213 A) : term459 A _45864.
Proof. exact (@lem3990372 A h1 _45864). Qed.
Lemma lem3990505 {A : Type'} (_45864 : A) : (term459 A _45864) = (term454 A _45864).
Proof. exact (eq_refl (term459 A _45864)). Qed.
Lemma lem3990506 {A : Type'} (_45864 : A) (h1 : term213 A) : term454 A _45864.
Proof. exact (EQ_MP (@lem3990505 A _45864) (@lem3990504 A _45864 h1)). Qed.
Lemma lem3990507 {A : Type'} (_45864 : A) (_45865 : A) (h1 : term213 A) : term460 A _45864 _45865.
Proof. exact (@lem3990506 A _45864 h1 _45865). Qed.
Lemma lem3990508 {A : Type'} (_45865 : A) (_45864 : A) : (term460 A _45864 _45865) = (term452 A _45865 _45864).
Proof. exact (eq_refl (term460 A _45864 _45865)). Qed.
Lemma lem3990509 {A : Type'} (_45865 : A) (_45864 : A) (h1 : term213 A) : term452 A _45865 _45864.
Proof. exact (EQ_MP (@lem3990508 A _45865 _45864) (@lem3990507 A _45864 _45865 h1)). Qed.
Lemma lem3990510 {A : Type'} (_45865 : A) (_45864 : A) (_45866 : A -> Prop) (h1 : term213 A) : term461 A _45865 _45864 _45866.
Proof. exact (@lem3990509 A _45865 _45864 h1 _45866). Qed.
Lemma lem3990511 {A : Type'} (_45865 : A) (_45864 : A) (_45866 : A -> Prop) : (term461 A _45865 _45864 _45866) = (term449 A _45865 _45864 _45866).
Proof. exact (eq_refl (term461 A _45865 _45864 _45866)). Qed.
Lemma lem3990512 {A : Type'} (_45865 : A) (_45864 : A) (_45866 : A -> Prop) (h1 : term213 A) : term449 A _45865 _45864 _45866.
Proof. exact (EQ_MP (@lem3990511 A _45865 _45864 _45866) (@lem3990510 A _45865 _45864 _45866 h1)). Qed.
Lemma lem3990551 {A B : Type'} (_45830 : A) (_45831 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term439 A B f x s _45830 _45831.
Proof. exact (EQ_MP (@lem3990406 A B f x s _45830 _45831) (@lem3990405 A B _45830 _45831 f x s h1)). Qed.
Lemma lem3990595 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term450 A x'' y.
Proof. exact (proj2 (@lem3989958 A B f s x'' y h1)). Qed.
Lemma lem3990607 {A : Type'} (_45845 : A) (_45844 : A) (_45846 : A -> Prop) (h1 : term213 A) : term462 A _45845 _45844 _45846.
Proof. exact (proj2 (@lem3990452 A _45845 _45844 _45846 h1)). Qed.
Lemma lem3990633 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term124 A x s.
Proof. exact (h1). Qed.
Lemma lem3990649 {A B : Type'} (_45850 : A) (_45851 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term439 A B f x s _45850 _45851.
Proof. exact (EQ_MP (@lem3990466 A B f x s _45850 _45851) (@lem3990465 A B _45850 _45851 f x s h1)). Qed.
Lemma lem3990693 {A : Type'} (_45866 : A -> Prop) (_45864 : A) (_45865 : A) (h1 : term213 A) : term463 A _45866 _45864 _45865.
Proof. exact (proj1 (@lem3990512 A _45865 _45864 _45866 h1)). Qed.
Lemma lem3990699 {A : Type'} (_45865 : A) (_45864 : A) (_45866 : A -> Prop) (h1 : term213 A) : term462 A _45865 _45864 _45866.
Proof. exact (proj2 (@lem3990512 A _45865 _45864 _45866 h1)). Qed.
Lemma lem3990907 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : (@I (A -> B) f x'') = (@I (A -> B) f y).
Proof. exact (proj1 (@lem3989954 A B f s x'' y h1)). Qed.
Lemma lem3990908 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term464 A B x'' f y.
Proof. exact (fun h0 : term437 A B x'' f y => @lem3990907 A B f s x'' y h1). Qed.
Lemma lem3990910 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3990911 {A B : Type'} (x'' : A) (f : A -> B) (y : A) : (term464 A B x'' f y) = ((@I (A -> B) f x'') = (@I (A -> B) f y)).
Proof. exact (@lem3990910 ((@I (A -> B) f x'') = (@I (A -> B) f y))). Qed.
Lemma lem3990912 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : (@I (A -> B) f x'') = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem3990911 A B x'' f y) (@lem3990908 A B f s x'' y h1)). Qed.
Lemma lem3990914 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : @IN A y s.
Proof. exact (proj1 (@lem3989956 A B f s x'' y h1)). Qed.
Lemma lem3990915 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term466 A y s.
Proof. exact (fun h0 : term124 A y s => @lem3990914 A B f s x'' y h1). Qed.
Lemma lem3990917 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3990918 {A : Type'} (y : A) (s : A -> Prop) : (term466 A y s) = (@IN A y s).
Proof. exact (@lem3990917 (@IN A y s)). Qed.
Lemma lem3990919 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : @IN A y s.
Proof. exact (EQ_MP (@lem3990918 A y s) (@lem3990915 A B f s x'' y h1)). Qed.
Lemma lem3990921 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3990922 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) : (term462 A _45845 _45844 _45846) = (term468 A _45844 _45845 _45846).
Proof. exact (@lem3990921 (term124 A _45844 _45846) (term259 A _45844 _45845 _45846)). Qed.
Lemma lem3990924 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3990925 {A : Type'} (_45844 : A) (_45846 : A -> Prop) : (term470 A _45844 _45846) = (@IN A _45844 _45846).
Proof. exact (@lem3990924 (@IN A _45844 _45846)). Qed.
Lemma lem3990926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3990927 {A : Type'} (_45844 : A) (_45846 : A -> Prop) : (term471 A _45844 _45846) = (term472 A _45844 _45846).
Proof. exact (MK_COMB (@lem3990926) (@lem3990925 A _45844 _45846)). Qed.
Lemma lem3990928 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) : (term259 A _45844 _45845 _45846) = (term259 A _45844 _45845 _45846).
Proof. exact (eq_refl (term259 A _45844 _45845 _45846)). Qed.
Lemma lem3990929 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) : (term468 A _45844 _45845 _45846) = (term473 A _45844 _45845 _45846).
Proof. exact (MK_COMB (@lem3990927 A _45844 _45846) (@lem3990928 A _45844 _45845 _45846)). Qed.
Lemma lem3990930 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) : (term462 A _45845 _45844 _45846) = (term473 A _45844 _45845 _45846).
Proof. exact (TRANS (@lem3990922 A _45844 _45845 _45846) (@lem3990929 A _45844 _45845 _45846)). Qed.
Lemma lem3990933 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) (h1 : term213 A) : term473 A _45844 _45845 _45846.
Proof. exact (EQ_MP (@lem3990930 A _45844 _45845 _45846) (@lem3990607 A _45845 _45844 _45846 h1)). Qed.
Lemma lem3990934 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) (h1 : term213 A) : term473 A _45844 _45845 _45846.
Proof. exact (@lem3990933 A _45844 _45845 _45846 h1). Qed.
Lemma lem3990935 {A : Type'} (y : A) (_45845 : A) (s : A -> Prop) (h1 : term213 A) : term473 A y _45845 s.
Proof. exact (@lem3990934 A y _45845 s h1). Qed.
Lemma lem3990938 {A B : Type'} (_45845 : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A y _45845 s.
Proof. exact (@lem3990935 A y _45845 s h1 (@lem3990919 A B f s x'' y h2)). Qed.
Lemma lem3990939 {A B : Type'} (_45845 : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A y _45845 s.
Proof. exact (@lem3990938 A B _45845 f s x'' y h1 h2). Qed.
Lemma lem3990940 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A y x s.
Proof. exact (@lem3990939 A B x f s x'' y h1 h2). Qed.
Lemma lem3990941 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term474 A y x s.
Proof. exact (fun h0 : term475 A y x s => @lem3990940 A B x f s x'' y h1 h2). Qed.
Lemma lem3990943 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3990944 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term474 A y x s) = (term259 A y x s).
Proof. exact (@lem3990943 (term259 A y x s)). Qed.
Lemma lem3990945 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A y x s.
Proof. exact (EQ_MP (@lem3990944 A y x s) (@lem3990941 A B x f s x'' y h1 h2)). Qed.
Lemma lem3990947 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : @IN A x'' s.
Proof. exact (proj1 (@lem3989958 A B f s x'' y h1)). Qed.
Lemma lem3990948 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term466 A x'' s.
Proof. exact (fun h0 : term124 A x'' s => @lem3990947 A B f s x'' y h1). Qed.
Lemma lem3990950 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3990951 {A : Type'} (x'' : A) (s : A -> Prop) : (term466 A x'' s) = (@IN A x'' s).
Proof. exact (@lem3990950 (@IN A x'' s)). Qed.
Lemma lem3990952 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : @IN A x'' s.
Proof. exact (EQ_MP (@lem3990951 A x'' s) (@lem3990948 A B f s x'' y h1)). Qed.
Lemma lem3990954 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) (h1 : term213 A) : term473 A _45844 _45845 _45846.
Proof. exact (EQ_MP (@lem3990930 A _45844 _45845 _45846) (@lem3990607 A _45845 _45844 _45846 h1)). Qed.
Lemma lem3990955 {A : Type'} (_45844 : A) (_45845 : A) (_45846 : A -> Prop) (h1 : term213 A) : term473 A _45844 _45845 _45846.
Proof. exact (@lem3990954 A _45844 _45845 _45846 h1). Qed.
Lemma lem3990956 {A : Type'} (x'' : A) (_45845 : A) (s : A -> Prop) (h1 : term213 A) : term473 A x'' _45845 s.
Proof. exact (@lem3990955 A x'' _45845 s h1). Qed.
Lemma lem3990959 {A B : Type'} (_45845 : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A x'' _45845 s.
Proof. exact (@lem3990956 A x'' _45845 s h1 (@lem3990952 A B f s x'' y h2)). Qed.
Lemma lem3990960 {A B : Type'} (_45845 : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A x'' _45845 s.
Proof. exact (@lem3990959 A B _45845 f s x'' y h1 h2). Qed.
Lemma lem3990961 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A x'' x s.
Proof. exact (@lem3990960 A B x f s x'' y h1 h2). Qed.
Lemma lem3990962 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term474 A x'' x s.
Proof. exact (fun h0 : term475 A x'' x s => @lem3990961 A B x f s x'' y h1 h2). Qed.
Lemma lem3990964 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3990965 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) : (term474 A x'' x s) = (term259 A x'' x s).
Proof. exact (@lem3990964 (term259 A x'' x s)). Qed.
Lemma lem3990966 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term259 A x'' x s.
Proof. exact (EQ_MP (@lem3990965 A x'' x s) (@lem3990962 A B x f s x'' y h1 h2)). Qed.
Lemma lem3990984 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3990985 {A : Type'} (x : A) (s : A -> Prop) (_45830 : A) (_45831 : A) : (term341 A x s _45830 _45831) = (term477 A x s _45830 _45831).
Proof. exact (@lem3990984 (term475 A _45830 x s) (term475 A _45831 x s) (_45830 = _45831)). Qed.
Lemma lem3990999 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3991000 {A : Type'} (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term478 A x s _45830 _45831) = (term479 A _45830 _45831 x s).
Proof. exact (@lem3990999 (_45830 = _45831) (term475 A _45831 x s)). Qed.
Lemma lem3991008 {A : Type'} (_45830 : A) (x : A) (s : A -> Prop) : (term339 A _45830 x s) = (term339 A _45830 x s).
Proof. exact (eq_refl (term339 A _45830 x s)). Qed.
Lemma lem3991009 {A : Type'} (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term477 A x s _45830 _45831) = (term480 A _45830 _45831 x s).
Proof. exact (MK_COMB (@lem3991008 A _45830 x s) (@lem3991000 A _45830 _45831 x s)). Qed.
Lemma lem3991013 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991014 {A : Type'} (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term480 A _45830 _45831 x s) = (term481 A _45830 _45831 x s).
Proof. exact (@lem3991013 (_45830 = _45831) (term475 A _45830 x s) (term475 A _45831 x s)). Qed.
Lemma lem3991032 {A : Type'} (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term477 A x s _45830 _45831) = (term481 A _45830 _45831 x s).
Proof. exact (TRANS (@lem3991009 A _45830 _45831 x s) (@lem3991014 A _45830 _45831 x s)). Qed.
Lemma lem3991033 {A : Type'} (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term341 A x s _45830 _45831) = (term481 A _45830 _45831 x s).
Proof. exact (TRANS (@lem3990985 A x s _45830 _45831) (@lem3991032 A _45830 _45831 x s)). Qed.
Lemma lem3991034 {A B : Type'} (_45830 : A) (f : A -> B) (_45831 : A) : (term438 A B _45830 f _45831) = (term438 A B _45830 f _45831).
Proof. exact (eq_refl (term438 A B _45830 f _45831)). Qed.
Lemma lem3991035 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45830 _45831) = (term482 A B f _45830 _45831 x s).
Proof. exact (MK_COMB (@lem3991034 A B _45830 f _45831) (@lem3991033 A _45830 _45831 x s)). Qed.
Lemma lem3991039 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991040 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term482 A B f _45830 _45831 x s) = (term483 A B f _45830 _45831 x s).
Proof. exact (@lem3991039 (_45830 = _45831) (term437 A B _45830 f _45831) (term484 A _45830 _45831 x s)). Qed.
Lemma lem3991070 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45830 _45831) = (term483 A B f _45830 _45831 x s).
Proof. exact (TRANS (@lem3991035 A B f _45830 _45831 x s) (@lem3991040 A B f _45830 _45831 x s)). Qed.
Lemma lem3991071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3991072 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term485 A B f x s _45830 _45831) = (term486 A B f _45830 _45831 x s).
Proof. exact (MK_COMB (@lem3991071) (@lem3991070 A B f _45830 _45831 x s)). Qed.
Lemma lem3991100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3991101 {A : Type'} (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term484 A _45831 _45830 x s) = (term484 A _45830 _45831 x s).
Proof. exact (@lem3991100 (term475 A _45830 x s) (term475 A _45831 x s)). Qed.
Lemma lem3991107 {A B : Type'} (_45830 : A) (f : A -> B) (_45831 : A) : (term438 A B _45830 f _45831) = (term438 A B _45830 f _45831).
Proof. exact (eq_refl (term438 A B _45830 f _45831)). Qed.
Lemma lem3991108 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term487 A B f _45831 _45830 x s) = (term488 A B f _45830 _45831 x s).
Proof. exact (MK_COMB (@lem3991107 A B _45830 f _45831) (@lem3991101 A _45830 _45831 x s)). Qed.
Lemma lem3991119 {A : Type'} (_45830 : A) (_45831 : A) : (term489 A _45830 _45831) = (term489 A _45830 _45831).
Proof. exact (eq_refl (term489 A _45830 _45831)). Qed.
Lemma lem3991120 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : (term490 A B f _45831 _45830 x s) = (term483 A B f _45830 _45831 x s).
Proof. exact (MK_COMB (@lem3991119 A _45830 _45831) (@lem3991108 A B f _45830 _45831 x s)). Qed.
Lemma lem3991131 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : ((term439 A B f x s _45830 _45831) = (term490 A B f _45831 _45830 x s)) = ((term483 A B f _45830 _45831 x s) = (term483 A B f _45830 _45831 x s)).
Proof. exact (MK_COMB (@lem3991072 A B f _45830 _45831 x s) (@lem3991120 A B f _45830 _45831 x s)). Qed.
Lemma lem3991133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3991134 (x : Prop) : (x = x) = True.
Proof. exact (@lem3991133 Prop x). Qed.
Lemma lem3991135 {A B : Type'} (f : A -> B) (_45830 : A) (_45831 : A) (x : A) (s : A -> Prop) : ((term483 A B f _45830 _45831 x s) = (term483 A B f _45830 _45831 x s)) = True.
Proof. exact (@lem3991134 (term483 A B f _45830 _45831 x s)). Qed.
Lemma lem3991136 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : ((term439 A B f x s _45830 _45831) = (term490 A B f _45831 _45830 x s)) = True.
Proof. exact (TRANS (@lem3991131 A B f _45830 _45831 x s) (@lem3991135 A B f _45830 _45831 x s)). Qed.
Lemma lem3991137 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : True = ((term439 A B f x s _45830 _45831) = (term490 A B f _45831 _45830 x s)).
Proof. exact (SYM (@lem3991136 A B f _45831 _45830 x s)). Qed.
Lemma lem3991138 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45830 _45831) = (term490 A B f _45831 _45830 x s).
Proof. exact (EQ_MP (@lem3991137 A B f _45831 _45830 x s) (@lem0)). Qed.
Lemma lem3991139 {A B : Type'} (_45831 : A) (_45830 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term490 A B f _45831 _45830 x s.
Proof. exact (EQ_MP (@lem3991138 A B f _45831 _45830 x s) (@lem3990551 A B _45830 _45831 f x s h1)). Qed.
Lemma lem3991141 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3991142 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45830 : A) (_45831 : A) : (term490 A B f _45831 _45830 x s) = (term491 A B f x s _45830 _45831).
Proof. exact (@lem3991141 (term487 A B f _45831 _45830 x s) (_45830 = _45831)). Qed.
Lemma lem3991144 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991145 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term494 A B f _45831 _45830 x s) = (term495 A B f _45831 _45830 x s).
Proof. exact (@lem3991144 (term437 A B _45830 f _45831) (term484 A _45831 _45830 x s)). Qed.
Lemma lem3991147 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991148 {A B : Type'} (_45830 : A) (f : A -> B) (_45831 : A) : (term496 A B _45830 f _45831) = ((@I (A -> B) f _45830) = (@I (A -> B) f _45831)).
Proof. exact (@lem3991147 ((@I (A -> B) f _45830) = (@I (A -> B) f _45831))). Qed.
Lemma lem3991149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991150 {A B : Type'} (_45830 : A) (f : A -> B) (_45831 : A) : (term497 A B _45830 f _45831) = (term444 A B _45830 f _45831).
Proof. exact (MK_COMB (@lem3991149) (@lem3991148 A B _45830 f _45831)). Qed.
Lemma lem3991152 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991153 {A : Type'} (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term498 A _45831 _45830 x s) = (term499 A _45831 _45830 x s).
Proof. exact (@lem3991152 (term475 A _45831 x s) (term475 A _45830 x s)). Qed.
Lemma lem3991155 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991156 {A : Type'} (_45831 : A) (x : A) (s : A -> Prop) : (term500 A _45831 x s) = (term259 A _45831 x s).
Proof. exact (@lem3991155 (term259 A _45831 x s)). Qed.
Lemma lem3991157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991158 {A : Type'} (_45831 : A) (x : A) (s : A -> Prop) : (term501 A _45831 x s) = (term502 A _45831 x s).
Proof. exact (MK_COMB (@lem3991157) (@lem3991156 A _45831 x s)). Qed.
Lemma lem3991160 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991161 {A : Type'} (_45830 : A) (x : A) (s : A -> Prop) : (term500 A _45830 x s) = (term259 A _45830 x s).
Proof. exact (@lem3991160 (term259 A _45830 x s)). Qed.
Lemma lem3991162 {A : Type'} (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term499 A _45831 _45830 x s) = (term503 A _45831 _45830 x s).
Proof. exact (MK_COMB (@lem3991158 A _45831 x s) (@lem3991161 A _45830 x s)). Qed.
Lemma lem3991163 {A : Type'} (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term498 A _45831 _45830 x s) = (term503 A _45831 _45830 x s).
Proof. exact (TRANS (@lem3991153 A _45831 _45830 x s) (@lem3991162 A _45831 _45830 x s)). Qed.
Lemma lem3991164 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term495 A B f _45831 _45830 x s) = (term504 A B f _45831 _45830 x s).
Proof. exact (MK_COMB (@lem3991150 A B _45830 f _45831) (@lem3991163 A _45831 _45830 x s)). Qed.
Lemma lem3991165 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term494 A B f _45831 _45830 x s) = (term504 A B f _45831 _45830 x s).
Proof. exact (TRANS (@lem3991145 A B f _45831 _45830 x s) (@lem3991164 A B f _45831 _45830 x s)). Qed.
Lemma lem3991166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3991167 {A B : Type'} (f : A -> B) (_45831 : A) (_45830 : A) (x : A) (s : A -> Prop) : (term505 A B f _45831 _45830 x s) = (term506 A B f _45831 _45830 x s).
Proof. exact (MK_COMB (@lem3991166) (@lem3991165 A B f _45831 _45830 x s)). Qed.
Lemma lem3991168 {A : Type'} (_45830 : A) (_45831 : A) : (_45830 = _45831) = (_45830 = _45831).
Proof. exact (eq_refl (_45830 = _45831)). Qed.
Lemma lem3991169 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45830 : A) (_45831 : A) : (term491 A B f x s _45830 _45831) = (term507 A B f x s _45830 _45831).
Proof. exact (MK_COMB (@lem3991167 A B f _45831 _45830 x s) (@lem3991168 A _45830 _45831)). Qed.
Lemma lem3991170 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45830 : A) (_45831 : A) : (term490 A B f _45831 _45830 x s) = (term507 A B f x s _45830 _45831).
Proof. exact (TRANS (@lem3991142 A B f x s _45830 _45831) (@lem3991169 A B f x s _45830 _45831)). Qed.
Lemma lem3991172 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term503 A y x'' x s.
Proof. exact (conj (@lem3990945 A B x f s x'' y h1 h2) (@lem3990966 A B x f s x'' y h1 h2)). Qed.
Lemma lem3991173 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x'' y) : term504 A B f y x'' x s.
Proof. exact (conj (@lem3990912 A B f s x'' y h2) (@lem3991172 A B x f s x'' y h1 h2)). Qed.
Lemma lem3991175 {A B : Type'} (_45830 : A) (_45831 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s _45830 _45831.
Proof. exact (EQ_MP (@lem3991170 A B f x s _45830 _45831) (@lem3991139 A B _45831 _45830 f x s h1)). Qed.
Lemma lem3991176 {A B : Type'} (_45830 : A) (_45831 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s _45830 _45831.
Proof. exact (@lem3991175 A B _45830 _45831 f x s h1). Qed.
Lemma lem3991177 {A B : Type'} (x'' : A) (y : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s x'' y.
Proof. exact (@lem3991176 A B x'' y f x s h1). Qed.
Lemma lem3991180 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x'' y) : x'' = y.
Proof. exact (@lem3991177 A B x'' y f x s h2 (@lem3991173 A B x f s x'' y h1 h3)). Qed.
Lemma lem3991181 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x'' y) : term508 A x'' y.
Proof. exact (fun h0 : term450 A x'' y => @lem3991180 A B x f s x'' y h1 h2 h3). Qed.
Lemma lem3991183 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991184 {A : Type'} (x'' : A) (y : A) : (term508 A x'' y) = (x'' = y).
Proof. exact (@lem3991183 (x'' = y)). Qed.
Lemma lem3991185 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x'' y) : x'' = y.
Proof. exact (EQ_MP (@lem3991184 A x'' y) (@lem3991181 A B x f s x'' y h1 h2 h3)). Qed.
Lemma lem3991188 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3991190 {A : Type'} (x'' : A) (y : A) : (term450 A x'' y) = (term509 A x'' y).
Proof. exact (@lem3991188 (x'' = y)). Qed.
Lemma lem3991193 {A B : Type'} (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term446 A B f s x'' y) : term509 A x'' y.
Proof. exact (EQ_MP (@lem3991190 A x'' y) (@lem3990595 A B f s x'' y h1)). Qed.
Lemma lem3991196 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x'' y) : False.
Proof. exact (@lem3991193 A B f s x'' y h3 (@lem3991185 A B x f s x'' y h1 h2 h3)). Qed.
Lemma lem3991197 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x'' y) : term510.
Proof. exact (fun h0 : ~ False => @lem3991196 A B x f s x'' y h1 h2 h3). Qed.
Lemma lem3991199 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991200 : term510 = False.
Proof. exact (@lem3991199 False). Qed.
Lemma lem3991201 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x'' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x'' y) : False.
Proof. exact (EQ_MP (@lem3991200) (@lem3991197 A B x f s x'' y h1 h2 h3)). Qed.
Lemma lem3991252 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3991253 {A : Type'} (_45920 : A) (_45922 : A) (h1 : _45920 = _45922) : _45920 = _45922.
Proof. exact (h1). Qed.
Lemma lem3991254 {A : Type'} (_45921 : A -> Prop) (_45923 : A -> Prop) (h1 : _45921 = _45923) : _45921 = _45923.
Proof. exact (h1). Qed.
Lemma lem3991255 {A : Type'} (_45920 : A) (_45922 : A) (h1 : _45920 = _45922) : (@IN A _45920) = (@IN A _45922).
Proof. exact (MK_COMB (@lem3991252 A) (@lem3991253 A _45920 _45922 h1)). Qed.
Lemma lem3991256 {A : Type'} (_45920 : A) (_45922 : A) (_45921 : A -> Prop) (_45923 : A -> Prop) (h1 : _45920 = _45922) (h2 : _45921 = _45923) : (@IN A _45920 _45921) = (@IN A _45922 _45923).
Proof. exact (MK_COMB (@lem3991255 A _45920 _45922 h1) (@lem3991254 A _45921 _45923 h2)). Qed.
Lemma lem3991258 (b : Prop) (a : Prop) : term511 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3991259 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : term512 A _45922 _45923 _45920 _45921.
Proof. exact (@lem3991258 (@IN A _45922 _45923) (@IN A _45920 _45921)). Qed.
Lemma lem3991260 {A : Type'} (_45920 : A) (_45922 : A) (_45921 : A -> Prop) (_45923 : A -> Prop) (h1 : _45920 = _45922) (h2 : _45921 = _45923) : term513 A _45922 _45923 _45920 _45921.
Proof. exact (@lem3991259 A _45922 _45923 _45920 _45921 (@lem3991256 A _45920 _45922 _45921 _45923 h1 h2)). Qed.
Lemma lem3991261 {A : Type'} (_45923 : A -> Prop) (_45921 : A -> Prop) (_45920 : A) (_45922 : A) (h1 : _45920 = _45922) : term514 A _45922 _45923 _45920 _45921.
Proof. exact (fun h0 : _45921 = _45923 => @lem3991260 A _45920 _45922 _45921 _45923 h1 h0). Qed.
Lemma lem3991263 (a : Prop) (b : Prop) : (a -> b) = (term515 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3991264 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term514 A _45922 _45923 _45920 _45921) = (term516 A _45922 _45923 _45920 _45921).
Proof. exact (@lem3991263 (_45921 = _45923) (term513 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991265 {A : Type'} (_45923 : A -> Prop) (_45921 : A -> Prop) (_45920 : A) (_45922 : A) (h1 : _45920 = _45922) : term516 A _45922 _45923 _45920 _45921.
Proof. exact (EQ_MP (@lem3991264 A _45922 _45923 _45920 _45921) (@lem3991261 A _45923 _45921 _45920 _45922 h1)). Qed.
Lemma lem3991266 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : term517 A _45922 _45923 _45920 _45921.
Proof. exact (fun h0 : _45920 = _45922 => @lem3991265 A _45923 _45921 _45920 _45922 h0). Qed.
Lemma lem3991268 (a : Prop) (b : Prop) : (a -> b) = (term515 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3991269 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term517 A _45922 _45923 _45920 _45921) = (term518 A _45922 _45923 _45920 _45921).
Proof. exact (@lem3991268 (_45920 = _45922) (term516 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991270 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : term518 A _45922 _45923 _45920 _45921.
Proof. exact (EQ_MP (@lem3991269 A _45922 _45923 _45920 _45921) (@lem3991266 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991373 {A : Type'} (x : A) (y : A) (z : A) : term519 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3991385 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : (@I (A -> B) f x) = (@I (A -> B) f x').
Proof. exact (proj1 (@lem3989883 A B x f x' s h1)). Qed.
Lemma lem3991386 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : term464 A B x f x'.
Proof. exact (fun h0 : term437 A B x f x' => @lem3991385 A B x f x' s h1). Qed.
Lemma lem3991388 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991389 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term464 A B x f x') = ((@I (A -> B) f x) = (@I (A -> B) f x')).
Proof. exact (@lem3991388 ((@I (A -> B) f x) = (@I (A -> B) f x'))). Qed.
Lemma lem3991390 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : (@I (A -> B) f x) = (@I (A -> B) f x').
Proof. exact (EQ_MP (@lem3991389 A B x f x') (@lem3991386 A B x f x' s h1)). Qed.
Lemma lem3991392 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : @IN A x' s.
Proof. exact (proj2 (@lem3989883 A B x f x' s h1)). Qed.
Lemma lem3991393 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : term466 A x' s.
Proof. exact (fun h0 : term124 A x' s => @lem3991392 A B x f x' s h1). Qed.
Lemma lem3991395 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991396 {A : Type'} (x' : A) (s : A -> Prop) : (term466 A x' s) = (@IN A x' s).
Proof. exact (@lem3991395 (@IN A x' s)). Qed.
Lemma lem3991397 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem3991396 A x' s) (@lem3991393 A B x f x' s h1)). Qed.
Lemma lem3991399 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3991400 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term462 A _45865 _45864 _45866) = (term468 A _45864 _45865 _45866).
Proof. exact (@lem3991399 (term124 A _45864 _45866) (term259 A _45864 _45865 _45866)). Qed.
Lemma lem3991402 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991403 {A : Type'} (_45864 : A) (_45866 : A -> Prop) : (term470 A _45864 _45866) = (@IN A _45864 _45866).
Proof. exact (@lem3991402 (@IN A _45864 _45866)). Qed.
Lemma lem3991404 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3991405 {A : Type'} (_45864 : A) (_45866 : A -> Prop) : (term471 A _45864 _45866) = (term472 A _45864 _45866).
Proof. exact (MK_COMB (@lem3991404) (@lem3991403 A _45864 _45866)). Qed.
Lemma lem3991406 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term259 A _45864 _45865 _45866) = (term259 A _45864 _45865 _45866).
Proof. exact (eq_refl (term259 A _45864 _45865 _45866)). Qed.
Lemma lem3991407 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term468 A _45864 _45865 _45866) = (term473 A _45864 _45865 _45866).
Proof. exact (MK_COMB (@lem3991405 A _45864 _45866) (@lem3991406 A _45864 _45865 _45866)). Qed.
Lemma lem3991408 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term462 A _45865 _45864 _45866) = (term473 A _45864 _45865 _45866).
Proof. exact (TRANS (@lem3991400 A _45864 _45865 _45866) (@lem3991407 A _45864 _45865 _45866)). Qed.
Lemma lem3991411 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) (h1 : term213 A) : term473 A _45864 _45865 _45866.
Proof. exact (EQ_MP (@lem3991408 A _45864 _45865 _45866) (@lem3990699 A _45865 _45864 _45866 h1)). Qed.
Lemma lem3991412 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) (h1 : term213 A) : term473 A _45864 _45865 _45866.
Proof. exact (@lem3991411 A _45864 _45865 _45866 h1). Qed.
Lemma lem3991413 {A : Type'} (x' : A) (_45865 : A) (s : A -> Prop) (h1 : term213 A) : term473 A x' _45865 s.
Proof. exact (@lem3991412 A x' _45865 s h1). Qed.
Lemma lem3991416 {A B : Type'} (_45865 : A) (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term259 A x' _45865 s.
Proof. exact (@lem3991413 A x' _45865 s h1 (@lem3991397 A B x f x' s h2)). Qed.
Lemma lem3991417 {A B : Type'} (_45865 : A) (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term259 A x' _45865 s.
Proof. exact (@lem3991416 A B _45865 x f x' s h1 h2). Qed.
Lemma lem3991418 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term259 A x' x s.
Proof. exact (@lem3991417 A B x x f x' s h1 h2). Qed.
Lemma lem3991419 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term474 A x' x s.
Proof. exact (fun h0 : term475 A x' x s => @lem3991418 A B x f x' s h1 h2). Qed.
Lemma lem3991421 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991422 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term474 A x' x s) = (term259 A x' x s).
Proof. exact (@lem3991421 (term259 A x' x s)). Qed.
Lemma lem3991423 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term259 A x' x s.
Proof. exact (EQ_MP (@lem3991422 A x' x s) (@lem3991419 A B x f x' s h1 h2)). Qed.
Lemma lem3991425 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3991426 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3991425 A x). Qed.
Lemma lem3991427 {A : Type'} (x : A) : term520 A x.
Proof. exact (fun h0 : term521 A x => @lem3991426 A x). Qed.
Lemma lem3991429 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991430 {A : Type'} (x : A) : (term520 A x) = (x = x).
Proof. exact (@lem3991429 (x = x)). Qed.
Lemma lem3991431 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3991430 A x) (@lem3991427 A x)). Qed.
Lemma lem3991433 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3991434 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term463 A _45866 _45864 _45865) = (term522 A _45864 _45865 _45866).
Proof. exact (@lem3991433 (term450 A _45864 _45865) (term259 A _45864 _45865 _45866)). Qed.
Lemma lem3991436 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991437 {A : Type'} (_45864 : A) (_45865 : A) : (term523 A _45864 _45865) = (_45864 = _45865).
Proof. exact (@lem3991436 (_45864 = _45865)). Qed.
Lemma lem3991438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3991439 {A : Type'} (_45864 : A) (_45865 : A) : (term524 A _45864 _45865) = (term525 A _45864 _45865).
Proof. exact (MK_COMB (@lem3991438) (@lem3991437 A _45864 _45865)). Qed.
Lemma lem3991440 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term259 A _45864 _45865 _45866) = (term259 A _45864 _45865 _45866).
Proof. exact (eq_refl (term259 A _45864 _45865 _45866)). Qed.
Lemma lem3991441 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term522 A _45864 _45865 _45866) = (term526 A _45864 _45865 _45866).
Proof. exact (MK_COMB (@lem3991439 A _45864 _45865) (@lem3991440 A _45864 _45865 _45866)). Qed.
Lemma lem3991442 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) : (term463 A _45866 _45864 _45865) = (term526 A _45864 _45865 _45866).
Proof. exact (TRANS (@lem3991434 A _45864 _45865 _45866) (@lem3991441 A _45864 _45865 _45866)). Qed.
Lemma lem3991445 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) (h1 : term213 A) : term526 A _45864 _45865 _45866.
Proof. exact (EQ_MP (@lem3991442 A _45864 _45865 _45866) (@lem3990693 A _45866 _45864 _45865 h1)). Qed.
Lemma lem3991446 {A : Type'} (_45864 : A) (_45865 : A) (_45866 : A -> Prop) (h1 : term213 A) : term526 A _45864 _45865 _45866.
Proof. exact (@lem3991445 A _45864 _45865 _45866 h1). Qed.
Lemma lem3991447 {A : Type'} (x : A) (_45866 : A -> Prop) (h1 : term213 A) : term527 A x _45866.
Proof. exact (@lem3991446 A x x _45866 h1). Qed.
Lemma lem3991450 {A : Type'} (x : A) (_45866 : A -> Prop) (h1 : term213 A) : term528 A x _45866.
Proof. exact (@lem3991447 A x _45866 h1 (@lem3991431 A x)). Qed.
Lemma lem3991451 {A : Type'} (x : A) (_45866 : A -> Prop) (h1 : term213 A) : term528 A x _45866.
Proof. exact (@lem3991450 A x _45866 h1). Qed.
Lemma lem3991452 {A : Type'} (x : A) (s : A -> Prop) (h1 : term213 A) : term528 A x s.
Proof. exact (@lem3991451 A x s h1). Qed.
Lemma lem3991453 {A : Type'} (x : A) (s : A -> Prop) (h1 : term213 A) : term529 A x s.
Proof. exact (fun h0 : term530 A x s => @lem3991452 A x s h1). Qed.
Lemma lem3991455 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991456 {A : Type'} (x : A) (s : A -> Prop) : (term529 A x s) = (term528 A x s).
Proof. exact (@lem3991455 (term528 A x s)). Qed.
Lemma lem3991457 {A : Type'} (x : A) (s : A -> Prop) (h1 : term213 A) : term528 A x s.
Proof. exact (EQ_MP (@lem3991456 A x s) (@lem3991453 A x s h1)). Qed.
Lemma lem3991475 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991476 {A : Type'} (x : A) (s : A -> Prop) (_45850 : A) (_45851 : A) : (term341 A x s _45850 _45851) = (term477 A x s _45850 _45851).
Proof. exact (@lem3991475 (term475 A _45850 x s) (term475 A _45851 x s) (_45850 = _45851)). Qed.
Lemma lem3991490 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3991491 {A : Type'} (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term478 A x s _45850 _45851) = (term479 A _45850 _45851 x s).
Proof. exact (@lem3991490 (_45850 = _45851) (term475 A _45851 x s)). Qed.
Lemma lem3991499 {A : Type'} (_45850 : A) (x : A) (s : A -> Prop) : (term339 A _45850 x s) = (term339 A _45850 x s).
Proof. exact (eq_refl (term339 A _45850 x s)). Qed.
Lemma lem3991500 {A : Type'} (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term477 A x s _45850 _45851) = (term480 A _45850 _45851 x s).
Proof. exact (MK_COMB (@lem3991499 A _45850 x s) (@lem3991491 A _45850 _45851 x s)). Qed.
Lemma lem3991504 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991505 {A : Type'} (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term480 A _45850 _45851 x s) = (term481 A _45850 _45851 x s).
Proof. exact (@lem3991504 (_45850 = _45851) (term475 A _45850 x s) (term475 A _45851 x s)). Qed.
Lemma lem3991523 {A : Type'} (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term477 A x s _45850 _45851) = (term481 A _45850 _45851 x s).
Proof. exact (TRANS (@lem3991500 A _45850 _45851 x s) (@lem3991505 A _45850 _45851 x s)). Qed.
Lemma lem3991524 {A : Type'} (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term341 A x s _45850 _45851) = (term481 A _45850 _45851 x s).
Proof. exact (TRANS (@lem3991476 A x s _45850 _45851) (@lem3991523 A _45850 _45851 x s)). Qed.
Lemma lem3991525 {A B : Type'} (_45850 : A) (f : A -> B) (_45851 : A) : (term438 A B _45850 f _45851) = (term438 A B _45850 f _45851).
Proof. exact (eq_refl (term438 A B _45850 f _45851)). Qed.
Lemma lem3991526 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45850 _45851) = (term482 A B f _45850 _45851 x s).
Proof. exact (MK_COMB (@lem3991525 A B _45850 f _45851) (@lem3991524 A _45850 _45851 x s)). Qed.
Lemma lem3991530 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991531 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term482 A B f _45850 _45851 x s) = (term483 A B f _45850 _45851 x s).
Proof. exact (@lem3991530 (_45850 = _45851) (term437 A B _45850 f _45851) (term484 A _45850 _45851 x s)). Qed.
Lemma lem3991561 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45850 _45851) = (term483 A B f _45850 _45851 x s).
Proof. exact (TRANS (@lem3991526 A B f _45850 _45851 x s) (@lem3991531 A B f _45850 _45851 x s)). Qed.
Lemma lem3991562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3991563 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term485 A B f x s _45850 _45851) = (term486 A B f _45850 _45851 x s).
Proof. exact (MK_COMB (@lem3991562) (@lem3991561 A B f _45850 _45851 x s)). Qed.
Lemma lem3991591 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3991592 {A : Type'} (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term484 A _45851 _45850 x s) = (term484 A _45850 _45851 x s).
Proof. exact (@lem3991591 (term475 A _45850 x s) (term475 A _45851 x s)). Qed.
Lemma lem3991598 {A B : Type'} (_45850 : A) (f : A -> B) (_45851 : A) : (term438 A B _45850 f _45851) = (term438 A B _45850 f _45851).
Proof. exact (eq_refl (term438 A B _45850 f _45851)). Qed.
Lemma lem3991599 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term487 A B f _45851 _45850 x s) = (term488 A B f _45850 _45851 x s).
Proof. exact (MK_COMB (@lem3991598 A B _45850 f _45851) (@lem3991592 A _45850 _45851 x s)). Qed.
Lemma lem3991610 {A : Type'} (_45850 : A) (_45851 : A) : (term489 A _45850 _45851) = (term489 A _45850 _45851).
Proof. exact (eq_refl (term489 A _45850 _45851)). Qed.
Lemma lem3991611 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : (term490 A B f _45851 _45850 x s) = (term483 A B f _45850 _45851 x s).
Proof. exact (MK_COMB (@lem3991610 A _45850 _45851) (@lem3991599 A B f _45850 _45851 x s)). Qed.
Lemma lem3991622 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : ((term439 A B f x s _45850 _45851) = (term490 A B f _45851 _45850 x s)) = ((term483 A B f _45850 _45851 x s) = (term483 A B f _45850 _45851 x s)).
Proof. exact (MK_COMB (@lem3991563 A B f _45850 _45851 x s) (@lem3991611 A B f _45850 _45851 x s)). Qed.
Lemma lem3991624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3991625 (x : Prop) : (x = x) = True.
Proof. exact (@lem3991624 Prop x). Qed.
Lemma lem3991626 {A B : Type'} (f : A -> B) (_45850 : A) (_45851 : A) (x : A) (s : A -> Prop) : ((term483 A B f _45850 _45851 x s) = (term483 A B f _45850 _45851 x s)) = True.
Proof. exact (@lem3991625 (term483 A B f _45850 _45851 x s)). Qed.
Lemma lem3991627 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : ((term439 A B f x s _45850 _45851) = (term490 A B f _45851 _45850 x s)) = True.
Proof. exact (TRANS (@lem3991622 A B f _45850 _45851 x s) (@lem3991626 A B f _45850 _45851 x s)). Qed.
Lemma lem3991628 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : True = ((term439 A B f x s _45850 _45851) = (term490 A B f _45851 _45850 x s)).
Proof. exact (SYM (@lem3991627 A B f _45851 _45850 x s)). Qed.
Lemma lem3991629 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45850 _45851) = (term490 A B f _45851 _45850 x s).
Proof. exact (EQ_MP (@lem3991628 A B f _45851 _45850 x s) (@lem0)). Qed.
Lemma lem3991630 {A B : Type'} (_45851 : A) (_45850 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term490 A B f _45851 _45850 x s.
Proof. exact (EQ_MP (@lem3991629 A B f _45851 _45850 x s) (@lem3990649 A B _45850 _45851 f x s h1)). Qed.
Lemma lem3991632 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3991633 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45850 : A) (_45851 : A) : (term490 A B f _45851 _45850 x s) = (term491 A B f x s _45850 _45851).
Proof. exact (@lem3991632 (term487 A B f _45851 _45850 x s) (_45850 = _45851)). Qed.
Lemma lem3991635 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991636 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term494 A B f _45851 _45850 x s) = (term495 A B f _45851 _45850 x s).
Proof. exact (@lem3991635 (term437 A B _45850 f _45851) (term484 A _45851 _45850 x s)). Qed.
Lemma lem3991638 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991639 {A B : Type'} (_45850 : A) (f : A -> B) (_45851 : A) : (term496 A B _45850 f _45851) = ((@I (A -> B) f _45850) = (@I (A -> B) f _45851)).
Proof. exact (@lem3991638 ((@I (A -> B) f _45850) = (@I (A -> B) f _45851))). Qed.
Lemma lem3991640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991641 {A B : Type'} (_45850 : A) (f : A -> B) (_45851 : A) : (term497 A B _45850 f _45851) = (term444 A B _45850 f _45851).
Proof. exact (MK_COMB (@lem3991640) (@lem3991639 A B _45850 f _45851)). Qed.
Lemma lem3991643 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991644 {A : Type'} (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term498 A _45851 _45850 x s) = (term499 A _45851 _45850 x s).
Proof. exact (@lem3991643 (term475 A _45851 x s) (term475 A _45850 x s)). Qed.
Lemma lem3991646 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991647 {A : Type'} (_45851 : A) (x : A) (s : A -> Prop) : (term500 A _45851 x s) = (term259 A _45851 x s).
Proof. exact (@lem3991646 (term259 A _45851 x s)). Qed.
Lemma lem3991648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991649 {A : Type'} (_45851 : A) (x : A) (s : A -> Prop) : (term501 A _45851 x s) = (term502 A _45851 x s).
Proof. exact (MK_COMB (@lem3991648) (@lem3991647 A _45851 x s)). Qed.
Lemma lem3991651 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991652 {A : Type'} (_45850 : A) (x : A) (s : A -> Prop) : (term500 A _45850 x s) = (term259 A _45850 x s).
Proof. exact (@lem3991651 (term259 A _45850 x s)). Qed.
Lemma lem3991653 {A : Type'} (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term499 A _45851 _45850 x s) = (term503 A _45851 _45850 x s).
Proof. exact (MK_COMB (@lem3991649 A _45851 x s) (@lem3991652 A _45850 x s)). Qed.
Lemma lem3991654 {A : Type'} (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term498 A _45851 _45850 x s) = (term503 A _45851 _45850 x s).
Proof. exact (TRANS (@lem3991644 A _45851 _45850 x s) (@lem3991653 A _45851 _45850 x s)). Qed.
Lemma lem3991655 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term495 A B f _45851 _45850 x s) = (term504 A B f _45851 _45850 x s).
Proof. exact (MK_COMB (@lem3991641 A B _45850 f _45851) (@lem3991654 A _45851 _45850 x s)). Qed.
Lemma lem3991656 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term494 A B f _45851 _45850 x s) = (term504 A B f _45851 _45850 x s).
Proof. exact (TRANS (@lem3991636 A B f _45851 _45850 x s) (@lem3991655 A B f _45851 _45850 x s)). Qed.
Lemma lem3991657 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3991658 {A B : Type'} (f : A -> B) (_45851 : A) (_45850 : A) (x : A) (s : A -> Prop) : (term505 A B f _45851 _45850 x s) = (term506 A B f _45851 _45850 x s).
Proof. exact (MK_COMB (@lem3991657) (@lem3991656 A B f _45851 _45850 x s)). Qed.
Lemma lem3991659 {A : Type'} (_45850 : A) (_45851 : A) : (_45850 = _45851) = (_45850 = _45851).
Proof. exact (eq_refl (_45850 = _45851)). Qed.
Lemma lem3991660 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45850 : A) (_45851 : A) : (term491 A B f x s _45850 _45851) = (term507 A B f x s _45850 _45851).
Proof. exact (MK_COMB (@lem3991658 A B f _45851 _45850 x s) (@lem3991659 A _45850 _45851)). Qed.
Lemma lem3991661 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45850 : A) (_45851 : A) : (term490 A B f _45851 _45850 x s) = (term507 A B f x s _45850 _45851).
Proof. exact (TRANS (@lem3991633 A B f x s _45850 _45851) (@lem3991660 A B f x s _45850 _45851)). Qed.
Lemma lem3991663 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term531 A x' x s.
Proof. exact (conj (@lem3991423 A B x f x' s h1 h2) (@lem3991457 A x s h1)). Qed.
Lemma lem3991664 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term266 A B x f x' s) : term532 A B f x' x s.
Proof. exact (conj (@lem3991390 A B x f x' s h2) (@lem3991663 A B x f x' s h1 h2)). Qed.
Lemma lem3991666 {A B : Type'} (_45850 : A) (_45851 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s _45850 _45851.
Proof. exact (EQ_MP (@lem3991661 A B f x s _45850 _45851) (@lem3991630 A B _45851 _45850 f x s h1)). Qed.
Lemma lem3991667 {A B : Type'} (_45850 : A) (_45851 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s _45850 _45851.
Proof. exact (@lem3991666 A B _45850 _45851 f x s h1). Qed.
Lemma lem3991668 {A B : Type'} (x' : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term533 A B f s x x'.
Proof. exact (@lem3991667 A B x x' f x s h1). Qed.
Lemma lem3991671 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : x = x'.
Proof. exact (@lem3991668 A B x' f x s h2 (@lem3991664 A B x f x' s h1 h3)). Qed.
Lemma lem3991672 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : term508 A x x'.
Proof. exact (fun h0 : term450 A x x' => @lem3991671 A B x f x' s h1 h2 h3). Qed.
Lemma lem3991674 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991675 {A : Type'} (x : A) (x' : A) : (term508 A x x') = (x = x').
Proof. exact (@lem3991674 (x = x')). Qed.
Lemma lem3991676 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : x = x'.
Proof. exact (EQ_MP (@lem3991675 A x x') (@lem3991672 A B x f x' s h1 h2 h3)). Qed.
Lemma lem3991678 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3991679 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3991678 A x). Qed.
Lemma lem3991680 {A : Type'} (x : A) : term520 A x.
Proof. exact (fun h0 : term521 A x => @lem3991679 A x). Qed.
Lemma lem3991682 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991683 {A : Type'} (x : A) : (term520 A x) = (x = x).
Proof. exact (@lem3991682 (x = x)). Qed.
Lemma lem3991684 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3991683 A x) (@lem3991680 A x)). Qed.
Lemma lem3991702 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3991703 {A : Type'} (y : A) (x : A) (z : A) : (term534 A x y z) = (term535 A y x z).
Proof. exact (@lem3991702 (y = z) (term450 A x z)). Qed.
Lemma lem3991713 {A : Type'} (x : A) (y : A) : (term536 A x y) = (term536 A x y).
Proof. exact (eq_refl (term536 A x y)). Qed.
Lemma lem3991714 {A : Type'} (y : A) (x : A) (z : A) : (term519 A x y z) = (term537 A y x z).
Proof. exact (MK_COMB (@lem3991713 A x y) (@lem3991703 A y x z)). Qed.
Lemma lem3991718 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991719 {A : Type'} (y : A) (x : A) (z : A) : (term537 A y x z) = (term538 A y x z).
Proof. exact (@lem3991718 (y = z) (term450 A x y) (term450 A x z)). Qed.
Lemma lem3991741 {A : Type'} (y : A) (x : A) (z : A) : (term519 A x y z) = (term538 A y x z).
Proof. exact (TRANS (@lem3991714 A y x z) (@lem3991719 A y x z)). Qed.
Lemma lem3991742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3991743 {A : Type'} (y : A) (x : A) (z : A) : (term539 A x y z) = (term540 A y x z).
Proof. exact (MK_COMB (@lem3991742) (@lem3991741 A y x z)). Qed.
Lemma lem3991765 {A : Type'} (y : A) (x : A) (z : A) : (term538 A y x z) = (term538 A y x z).
Proof. exact (eq_refl (term538 A y x z)). Qed.
Lemma lem3991766 {A : Type'} (y : A) (x : A) (z : A) : ((term519 A x y z) = (term538 A y x z)) = ((term538 A y x z) = (term538 A y x z)).
Proof. exact (MK_COMB (@lem3991743 A y x z) (@lem3991765 A y x z)). Qed.
Lemma lem3991768 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3991769 (x : Prop) : (x = x) = True.
Proof. exact (@lem3991768 Prop x). Qed.
Lemma lem3991770 {A : Type'} (y : A) (x : A) (z : A) : ((term538 A y x z) = (term538 A y x z)) = True.
Proof. exact (@lem3991769 (term538 A y x z)). Qed.
Lemma lem3991771 {A : Type'} (y : A) (x : A) (z : A) : ((term519 A x y z) = (term538 A y x z)) = True.
Proof. exact (TRANS (@lem3991766 A y x z) (@lem3991770 A y x z)). Qed.
Lemma lem3991772 {A : Type'} (y : A) (x : A) (z : A) : True = ((term519 A x y z) = (term538 A y x z)).
Proof. exact (SYM (@lem3991771 A y x z)). Qed.
Lemma lem3991773 {A : Type'} (y : A) (x : A) (z : A) : (term519 A x y z) = (term538 A y x z).
Proof. exact (EQ_MP (@lem3991772 A y x z) (@lem0)). Qed.
Lemma lem3991774 {A : Type'} (y : A) (x : A) (z : A) : term538 A y x z.
Proof. exact (EQ_MP (@lem3991773 A y x z) (@lem3991373 A x y z)). Qed.
Lemma lem3991776 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3991777 {A : Type'} (x : A) (y : A) (z : A) : (term538 A y x z) = (term541 A x y z).
Proof. exact (@lem3991776 (term542 A y x z) (y = z)). Qed.
Lemma lem3991779 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991780 {A : Type'} (y : A) (x : A) (z : A) : (term543 A y x z) = (term544 A y x z).
Proof. exact (@lem3991779 (term450 A x y) (term450 A x z)). Qed.
Lemma lem3991782 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991783 {A : Type'} (x : A) (y : A) : (term523 A x y) = (x = y).
Proof. exact (@lem3991782 (x = y)). Qed.
Lemma lem3991784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991785 {A : Type'} (x : A) (y : A) : (term545 A x y) = (term546 A x y).
Proof. exact (MK_COMB (@lem3991784) (@lem3991783 A x y)). Qed.
Lemma lem3991787 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991788 {A : Type'} (x : A) (z : A) : (term523 A x z) = (x = z).
Proof. exact (@lem3991787 (x = z)). Qed.
Lemma lem3991789 {A : Type'} (y : A) (x : A) (z : A) : (term544 A y x z) = (term547 A y x z).
Proof. exact (MK_COMB (@lem3991785 A x y) (@lem3991788 A x z)). Qed.
Lemma lem3991790 {A : Type'} (y : A) (x : A) (z : A) : (term543 A y x z) = (term547 A y x z).
Proof. exact (TRANS (@lem3991780 A y x z) (@lem3991789 A y x z)). Qed.
Lemma lem3991791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3991792 {A : Type'} (y : A) (x : A) (z : A) : (term548 A y x z) = (term549 A y x z).
Proof. exact (MK_COMB (@lem3991791) (@lem3991790 A y x z)). Qed.
Lemma lem3991793 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3991794 {A : Type'} (x : A) (y : A) (z : A) : (term541 A x y z) = (term550 A x y z).
Proof. exact (MK_COMB (@lem3991792 A y x z) (@lem3991793 A y z)). Qed.
Lemma lem3991795 {A : Type'} (x : A) (y : A) (z : A) : (term538 A y x z) = (term550 A x y z).
Proof. exact (TRANS (@lem3991777 A x y z) (@lem3991794 A x y z)). Qed.
Lemma lem3991797 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : term551 A x' x.
Proof. exact (conj (@lem3991676 A B x f x' s h1 h2 h3) (@lem3991684 A x)). Qed.
Lemma lem3991799 {A : Type'} (x : A) (y : A) (z : A) : term550 A x y z.
Proof. exact (EQ_MP (@lem3991795 A x y z) (@lem3991774 A y x z)). Qed.
Lemma lem3991800 {A : Type'} (x : A) (y : A) (z : A) : term550 A x y z.
Proof. exact (@lem3991799 A x y z). Qed.
Lemma lem3991801 {A : Type'} (x' : A) (x : A) : term552 A x' x.
Proof. exact (@lem3991800 A x x' x). Qed.
Lemma lem3991804 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : x' = x.
Proof. exact (@lem3991801 A x' x (@lem3991797 A B x f x' s h1 h2 h3)). Qed.
Lemma lem3991805 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : term508 A x' x.
Proof. exact (fun h0 : term450 A x' x => @lem3991804 A B x f x' s h1 h2 h3). Qed.
Lemma lem3991807 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991808 {A : Type'} (x' : A) (x : A) : (term508 A x' x) = (x' = x).
Proof. exact (@lem3991807 (x' = x)). Qed.
Lemma lem3991809 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : x' = x.
Proof. exact (EQ_MP (@lem3991808 A x' x) (@lem3991805 A B x f x' s h1 h2 h3)). Qed.
Lemma lem3991811 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3991812 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3991811 A x). Qed.
Lemma lem3991813 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem3991812 A s). Qed.
Lemma lem3991814 {A : Type'} (s : A -> Prop) : term553 A s.
Proof. exact (fun h0 : term554 A s => @lem3991813 A s). Qed.
Lemma lem3991816 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991817 {A : Type'} (s : A -> Prop) : (term553 A s) = (s = s).
Proof. exact (@lem3991816 (s = s)). Qed.
Lemma lem3991818 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3991817 A s) (@lem3991814 A s)). Qed.
Lemma lem3991820 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : @IN A x' s.
Proof. exact (proj2 (@lem3989883 A B x f x' s h1)). Qed.
Lemma lem3991821 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : term466 A x' s.
Proof. exact (fun h0 : term124 A x' s => @lem3991820 A B x f x' s h1). Qed.
Lemma lem3991823 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991824 {A : Type'} (x' : A) (s : A -> Prop) : (term466 A x' s) = (@IN A x' s).
Proof. exact (@lem3991823 (@IN A x' s)). Qed.
Lemma lem3991825 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem3991824 A x' s) (@lem3991821 A B x f x' s h1)). Qed.
Lemma lem3991843 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991844 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term516 A _45922 _45923 _45920 _45921) = (term555 A _45922 _45923 _45920 _45921).
Proof. exact (@lem3991843 (@IN A _45922 _45923) (term556 A _45921 _45923) (term124 A _45920 _45921)). Qed.
Lemma lem3991862 {A : Type'} (_45920 : A) (_45922 : A) : (term536 A _45920 _45922) = (term536 A _45920 _45922).
Proof. exact (eq_refl (term536 A _45920 _45922)). Qed.
Lemma lem3991863 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term518 A _45922 _45923 _45920 _45921) = (term557 A _45922 _45923 _45920 _45921).
Proof. exact (MK_COMB (@lem3991862 A _45920 _45922) (@lem3991844 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991867 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3991868 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term557 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921).
Proof. exact (@lem3991867 (@IN A _45922 _45923) (term450 A _45920 _45922) (term559 A _45923 _45920 _45921)). Qed.
Lemma lem3991898 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term518 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921).
Proof. exact (TRANS (@lem3991863 A _45922 _45923 _45920 _45921) (@lem3991868 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3991900 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term560 A _45922 _45923 _45920 _45921) = (term561 A _45922 _45923 _45920 _45921).
Proof. exact (MK_COMB (@lem3991899) (@lem3991898 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991930 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term558 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921).
Proof. exact (eq_refl (term558 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991931 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : ((term518 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921)) = ((term558 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921)).
Proof. exact (MK_COMB (@lem3991900 A _45922 _45923 _45920 _45921) (@lem3991930 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991933 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3991934 (x : Prop) : (x = x) = True.
Proof. exact (@lem3991933 Prop x). Qed.
Lemma lem3991935 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : ((term558 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921)) = True.
Proof. exact (@lem3991934 (term558 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991936 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : ((term518 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921)) = True.
Proof. exact (TRANS (@lem3991931 A _45922 _45923 _45920 _45921) (@lem3991935 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991937 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : True = ((term518 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921)).
Proof. exact (SYM (@lem3991936 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991938 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term518 A _45922 _45923 _45920 _45921) = (term558 A _45922 _45923 _45920 _45921).
Proof. exact (EQ_MP (@lem3991937 A _45922 _45923 _45920 _45921) (@lem0)). Qed.
Lemma lem3991939 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : term558 A _45922 _45923 _45920 _45921.
Proof. exact (EQ_MP (@lem3991938 A _45922 _45923 _45920 _45921) (@lem3991270 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991941 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3991942 {A : Type'} (_45920 : A) (_45921 : A -> Prop) (_45922 : A) (_45923 : A -> Prop) : (term558 A _45922 _45923 _45920 _45921) = (term562 A _45920 _45921 _45922 _45923).
Proof. exact (@lem3991941 (term563 A _45922 _45923 _45920 _45921) (@IN A _45922 _45923)). Qed.
Lemma lem3991944 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991945 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term564 A _45922 _45923 _45920 _45921) = (term565 A _45922 _45923 _45920 _45921).
Proof. exact (@lem3991944 (term450 A _45920 _45922) (term559 A _45923 _45920 _45921)). Qed.
Lemma lem3991947 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991948 {A : Type'} (_45920 : A) (_45922 : A) : (term523 A _45920 _45922) = (_45920 = _45922).
Proof. exact (@lem3991947 (_45920 = _45922)). Qed.
Lemma lem3991949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991950 {A : Type'} (_45920 : A) (_45922 : A) : (term545 A _45920 _45922) = (term546 A _45920 _45922).
Proof. exact (MK_COMB (@lem3991949) (@lem3991948 A _45920 _45922)). Qed.
Lemma lem3991952 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3991953 {A : Type'} (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term566 A _45923 _45920 _45921) = (term567 A _45923 _45920 _45921).
Proof. exact (@lem3991952 (term556 A _45921 _45923) (term124 A _45920 _45921)). Qed.
Lemma lem3991955 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991956 {A : Type'} (_45921 : A -> Prop) (_45923 : A -> Prop) : (term568 A _45921 _45923) = (_45921 = _45923).
Proof. exact (@lem3991955 (_45921 = _45923)). Qed.
Lemma lem3991957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3991958 {A : Type'} (_45921 : A -> Prop) (_45923 : A -> Prop) : (term569 A _45921 _45923) = (term570 A _45921 _45923).
Proof. exact (MK_COMB (@lem3991957) (@lem3991956 A _45921 _45923)). Qed.
Lemma lem3991960 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3991961 {A : Type'} (_45920 : A) (_45921 : A -> Prop) : (term470 A _45920 _45921) = (@IN A _45920 _45921).
Proof. exact (@lem3991960 (@IN A _45920 _45921)). Qed.
Lemma lem3991962 {A : Type'} (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term567 A _45923 _45920 _45921) = (term571 A _45923 _45920 _45921).
Proof. exact (MK_COMB (@lem3991958 A _45921 _45923) (@lem3991961 A _45920 _45921)). Qed.
Lemma lem3991963 {A : Type'} (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term566 A _45923 _45920 _45921) = (term571 A _45923 _45920 _45921).
Proof. exact (TRANS (@lem3991953 A _45923 _45920 _45921) (@lem3991962 A _45923 _45920 _45921)). Qed.
Lemma lem3991964 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term565 A _45922 _45923 _45920 _45921) = (term572 A _45922 _45923 _45920 _45921).
Proof. exact (MK_COMB (@lem3991950 A _45920 _45922) (@lem3991963 A _45923 _45920 _45921)). Qed.
Lemma lem3991965 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term564 A _45922 _45923 _45920 _45921) = (term572 A _45922 _45923 _45920 _45921).
Proof. exact (TRANS (@lem3991945 A _45922 _45923 _45920 _45921) (@lem3991964 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991966 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3991967 {A : Type'} (_45922 : A) (_45923 : A -> Prop) (_45920 : A) (_45921 : A -> Prop) : (term573 A _45922 _45923 _45920 _45921) = (term574 A _45922 _45923 _45920 _45921).
Proof. exact (MK_COMB (@lem3991966) (@lem3991965 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991968 {A : Type'} (_45922 : A) (_45923 : A -> Prop) : (@IN A _45922 _45923) = (@IN A _45922 _45923).
Proof. exact (eq_refl (@IN A _45922 _45923)). Qed.
Lemma lem3991969 {A : Type'} (_45920 : A) (_45921 : A -> Prop) (_45922 : A) (_45923 : A -> Prop) : (term562 A _45920 _45921 _45922 _45923) = (term575 A _45920 _45921 _45922 _45923).
Proof. exact (MK_COMB (@lem3991967 A _45922 _45923 _45920 _45921) (@lem3991968 A _45922 _45923)). Qed.
Lemma lem3991970 {A : Type'} (_45920 : A) (_45921 : A -> Prop) (_45922 : A) (_45923 : A -> Prop) : (term558 A _45922 _45923 _45920 _45921) = (term575 A _45920 _45921 _45922 _45923).
Proof. exact (TRANS (@lem3991942 A _45920 _45921 _45922 _45923) (@lem3991969 A _45920 _45921 _45922 _45923)). Qed.
Lemma lem3991972 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term266 A B x f x' s) : term576 A x' s.
Proof. exact (conj (@lem3991818 A s) (@lem3991825 A B x f x' s h1)). Qed.
Lemma lem3991973 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : term577 A x x' s.
Proof. exact (conj (@lem3991809 A B x f x' s h1 h2 h3) (@lem3991972 A B x f x' s h3)). Qed.
Lemma lem3991975 {A : Type'} (_45920 : A) (_45921 : A -> Prop) (_45922 : A) (_45923 : A -> Prop) : term575 A _45920 _45921 _45922 _45923.
Proof. exact (EQ_MP (@lem3991970 A _45920 _45921 _45922 _45923) (@lem3991939 A _45922 _45923 _45920 _45921)). Qed.
Lemma lem3991976 {A : Type'} (_45920 : A) (_45921 : A -> Prop) (_45922 : A) (_45923 : A -> Prop) : term575 A _45920 _45921 _45922 _45923.
Proof. exact (@lem3991975 A _45920 _45921 _45922 _45923). Qed.
Lemma lem3991977 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : term578 A x' x s.
Proof. exact (@lem3991976 A x' s x s). Qed.
Lemma lem3991980 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : @IN A x s.
Proof. exact (@lem3991977 A x' x s (@lem3991973 A B x f x' s h1 h2 h3)). Qed.
Lemma lem3991981 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : term466 A x s.
Proof. exact (fun h0 : term124 A x s => @lem3991980 A B x f x' s h1 h2 h3). Qed.
Lemma lem3991983 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3991984 {A : Type'} (x : A) (s : A -> Prop) : (term466 A x s) = (@IN A x s).
Proof. exact (@lem3991983 (@IN A x s)). Qed.
Lemma lem3991985 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term266 A B x f x' s) : @IN A x s.
Proof. exact (EQ_MP (@lem3991984 A x s) (@lem3991981 A B x f x' s h1 h2 h3)). Qed.
Lemma lem3991988 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3991990 {A : Type'} (x : A) (s : A -> Prop) : (term124 A x s) = (term579 A x s).
Proof. exact (@lem3991988 (@IN A x s)). Qed.
Lemma lem3991993 {A : Type'} (x : A) (s : A -> Prop) (h1 : term124 A x s) : term579 A x s.
Proof. exact (EQ_MP (@lem3991990 A x s) (@lem3990633 A x s h1)). Qed.
Lemma lem3991996 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : False.
Proof. exact (@lem3991993 A x s h3 (@lem3991985 A B x f x' s h1 h2 h4)). Qed.
Lemma lem3991997 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : term510.
Proof. exact (fun h0 : ~ False => @lem3991996 A B x f x' s h1 h2 h3 h4). Qed.
Lemma lem3991999 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3992000 : term510 = False.
Proof. exact (@lem3991999 False). Qed.
Lemma lem3992001 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : False.
Proof. exact (EQ_MP (@lem3992000) (@lem3991997 A B x f x' s h1 h2 h3 h4)). Qed.
Lemma lem3992002 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : (term124 A x s) = False.
Proof. exact (prop_ext (fun h5 : term124 A x s => @lem3992001 A B x f x' s h1 h2 h3 h4) (fun h5 : False => @lem3990633 A x s h3)). Qed.
Lemma lem3992003 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : False.
Proof. exact (EQ_MP (@lem3992002 A B x f x' s h1 h2 h3 h4) (@lem3990633 A x s h3)). Qed.
Lemma lem3992004 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : (term124 A x s) = False.
Proof. exact (prop_ext (fun h5 : term124 A x s => @lem3992003 A B x f x' s h1 h2 h3 h4) (fun h5 : False => @lem3990191 A x s h3)). Qed.
Lemma lem3992005 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : False.
Proof. exact (EQ_MP (@lem3992004 A B x f x' s h1 h2 h3 h4) (@lem3990191 A x s h3)). Qed.
Lemma lem3992006 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : (term124 A x s) = False.
Proof. exact (prop_ext (fun h5 : term124 A x s => @lem3992005 A B x f x' s h1 h2 h3 h4) (fun h5 : False => @lem3990191 A x s h3)). Qed.
Lemma lem3992007 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) : False.
Proof. exact (EQ_MP (@lem3992006 A B x f x' s h1 h2 h3 h4) (@lem3990191 A x s h3)). Qed.
Lemma lem3992008 {A B : Type'} (x : A) (x' : A) (x'' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) (h5 : term331 A B x'' y f s) : False.
Proof. exact (or_elim (@lem3989945 A B x'' y f s h5) (fun h0 : term446 A B f s x'' y => @lem3991201 A B x f s x'' y h1 h2 h0) (fun h0 : (term32 A B f s) = (@CARD A s) => @lem3992007 A B x f x' s h1 h2 h3 h4)). Qed.
Lemma lem3992009 {A B : Type'} (x : A) (x' : A) (x'' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) (h5 : term331 A B x'' y f s) : (term124 A x s) = False.
Proof. exact (prop_ext (fun h6 : term124 A x s => @lem3992008 A B x x' x'' y f s h1 h2 h3 h4 h5) (fun h6 : False => @lem3989536 A x s h3)). Qed.
Lemma lem3992010 {A B : Type'} (x : A) (x' : A) (x'' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) (h5 : term331 A B x'' y f s) : False.
Proof. exact (EQ_MP (@lem3992009 A B x x' x'' y f s h1 h2 h3 h4 h5) (@lem3989536 A x s h3)). Qed.
Lemma lem3992011 {A B : Type'} (x'' : A) (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term334 A B x'' f s) (h4 : term124 A x s) (h5 : term266 A B x f x' s) : False.
Proof. exact (ex_elim (@lem3989527 A B x'' f s h3) (fun y : A => fun h0 : term333 A B x'' f s y => @lem3992010 A B x x' x'' y f s h1 h2 h4 h5 h0)). Qed.
Lemma lem3992012 {A B : Type'} (x : A) (x' : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term124 A x s) (h4 : term266 A B x f x' s) (h5 : term48 A B f s) : False.
Proof. exact (ex_elim (@lem3988023 A B f s h5) (fun x'' : A => fun h0 : term335 A B f s x'' => @lem3992011 A B x'' x f x' s h1 h2 h0 h3 h4)). Qed.
Lemma lem3992013 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : False.
Proof. exact (ex_elim (@lem3988178 A B x f s h3) (fun x' : A => fun h0 : term267 A B x f s x' => @lem3992012 A B x x' f s h1 h2 h4 h0 h5)). Qed.
Lemma lem3992014 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term163 A B x f s) = False.
Proof. exact (prop_ext (fun h6 : term163 A B x f s => @lem3992013 A B x f s h1 h2 h3 h4 h5) (fun h6 : False => @lem3988178 A B x f s h3)). Qed.
Lemma lem3992015 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : False.
Proof. exact (EQ_MP (@lem3992014 A B x f s h1 h2 h3 h4 h5) (@lem3988178 A B x f s h3)). Qed.
Lemma lem3992016 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term124 A x s) = False.
Proof. exact (prop_ext (fun h6 : term124 A x s => @lem3992015 A B x f s h1 h2 h3 h4 h5) (fun h6 : False => @lem3988029 A x s h4)). Qed.
Lemma lem3992017 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : False.
Proof. exact (EQ_MP (@lem3992016 A B x f s h1 h2 h3 h4 h5) (@lem3988029 A x s h4)). Qed.
Lemma lem3992018 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : term219.
Proof. exact (fun h0 : term214 => @lem3992017 A B x f s h1 h2 h3 h4 h5). Qed.
Lemma lem3992019 : term219 = term220.
Proof. exact (@lem69 term214). Qed.
Lemma lem3992020 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : term220.
Proof. exact (EQ_MP (@lem3992019) (@lem3992018 A B x f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3992021 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term163 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : term223 B.
Proof. exact (fun h0 : term213 B => @lem3992020 A B x f s h1 h2 h3 h4 h5). Qed.
Lemma lem3992022 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : term124 A x s) (h4 : term48 A B f s) : term225 A B.
Proof. exact (fun h0 : term213 A => @lem3992021 A B x f s h0 h1 h2 h3 h4). Qed.
Lemma lem3992023 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : term124 A x s) (h4 : term48 A B f s) : term228 A B f s.
Proof. exact (fun h0 : term212 A B f s => @lem3992022 A B x f s h1 h2 h3 h4). Qed.
Lemma lem3992024 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term124 A x s) (h3 : term48 A B f s) : term230 A B x f s.
Proof. exact (fun h0 : term163 A B x f s => @lem3992023 A B x f s h1 h0 h2 h3). Qed.
Lemma lem3992025 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term124 A x s) (h2 : term48 A B f s) : term232 A B x f s.
Proof. exact (fun h0 : term125 A B f x s => @lem3992024 A B x f s h0 h1 h2). Qed.
Lemma lem3992026 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term124 A x s) (h2 : term48 A B f s) : term234 A B x f s.
Proof. exact (fun h0 : @FINITE A s => @lem3992025 A B x f s h1 h2). Qed.
Lemma lem3992027 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term237 A B x f s.
Proof. exact (fun h0 : term124 A x s => @lem3992026 A B x f s h0 h1). Qed.
Lemma lem3992028 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term239 A B x f s.
Proof. exact (fun h0 : term48 A B f s => @lem3992027 A B x f s h0). Qed.
Lemma lem3992033 {A B : Type'} (f : A -> B) (s : A -> Prop) : term243 A B f s.
Proof. exact (fun x : A => @lem3992028 A B x f s). Qed.
Lemma lem3992038 {A B : Type'} (s : A -> Prop) : term247 A B s.
Proof. exact (fun f : A -> B => @lem3992033 A B f s). Qed.
Lemma lem3992043 {A B : Type'} : term251 A B.
Proof. exact (fun s : A -> Prop => @lem3992038 A B s). Qed.
Lemma lem3992044 {A B : Type'} : term250 A B.
Proof. exact (EQ_MP (@lem3987861 A B) (@lem3992043 A B)). Qed.
Lemma lem3992045 {A B : Type'} (s : A -> Prop) : term580 A B s.
Proof. exact (@lem3992044 A B s). Qed.
Lemma lem3992046 {A B : Type'} (s : A -> Prop) : (term580 A B s) = (term246 A B s).
Proof. exact (eq_refl (term580 A B s)). Qed.
Lemma lem3992047 {A B : Type'} (s : A -> Prop) : term246 A B s.
Proof. exact (EQ_MP (@lem3992046 A B s) (@lem3992045 A B s)). Qed.
Lemma lem3992048 {A B : Type'} (s : A -> Prop) (f : A -> B) : term581 A B s f.
Proof. exact (@lem3992047 A B s f). Qed.
Lemma lem3992049 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term581 A B s f) = (term242 A B f s).
Proof. exact (eq_refl (term581 A B s f)). Qed.
Lemma lem3992050 {A B : Type'} (f : A -> B) (s : A -> Prop) : term242 A B f s.
Proof. exact (EQ_MP (@lem3992049 A B f s) (@lem3992048 A B s f)). Qed.
Lemma lem3992051 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : term582 A B f s x.
Proof. exact (@lem3992050 A B f s x). Qed.
Lemma lem3992052 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term582 A B f s x) = (term215 A B x f s).
Proof. exact (eq_refl (term582 A B f s x)). Qed.
Lemma lem3992053 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term215 A B x f s.
Proof. exact (EQ_MP (@lem3992052 A B x f s) (@lem3992051 A B f s x)). Qed.
Lemma lem3992055 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term215 A B x f s.
Proof. exact (@lem3987361 A B x f s (@lem3992053 A B x f s)). Qed.
Lemma lem3992056 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term236 A B x f s.
Proof. exact (@lem3992055 A B x f s (@lem3971726 A B f s h1)). Qed.
Lemma lem3992057 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term124 A x s) (h2 : term48 A B f s) : term233 A B x f s.
Proof. exact (@lem3992056 A B x f s h2 (@lem3971728 A x s h1)). Qed.
Lemma lem3992058 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : term231 A B x f s.
Proof. exact (@lem3992057 A B x f s h2 h3 (@lem3971727 A s h1)). Qed.
Lemma lem3992059 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : term229 A B x f s.
Proof. exact (@lem3992058 A B x f s h2 h3 h4 (@lem3971729 A B f x s h1)). Qed.
Lemma lem3992060 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term124 A x s) (h5 : term48 A B f s) : term227 A B f s.
Proof. exact (@lem3992059 A B x f s h1 h3 h4 h5 (@lem3987302 A B x f s h2)). Qed.
Lemma lem3992061 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term212 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : term224 A B.
Proof. exact (@lem3992060 A B x f s h1 h2 h3 h5 h6 (@lem3987340 A B f s h4)). Qed.
Lemma lem3992062 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term212 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : term222 B.
Proof. exact (@lem3992061 A B x f s h1 h2 h3 h4 h5 h6 (@lem3987341 A)). Qed.
Lemma lem3992063 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term212 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : term219.
Proof. exact (@lem3992062 A B x f s h1 h2 h3 h4 h5 h6 (@lem3987343 B)). Qed.
Lemma lem3992064 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term212 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : False.
Proof. exact (@lem3992063 A B x f s h1 h2 h3 h4 h5 h6 (@lem3987345)). Qed.
Lemma lem3992065 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term212 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : (term212 A B f s) = False.
Proof. exact (prop_ext (fun h7 : term212 A B f s => @lem3992064 A B x f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3987340 A B f s h4)). Qed.
Lemma lem3992066 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term212 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : False.
Proof. exact (EQ_MP (@lem3992065 A B x f s h1 h2 h3 h4 h5 h6) (@lem3987340 A B f s h4)). Qed.
Lemma lem3992067 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term124 A x s) (h5 : term48 A B f s) : term211 A B f s.
Proof. exact (fun h0 : term212 A B f s => @lem3992066 A B x f s h1 h2 h3 h0 h4 h5). Qed.
Lemma lem3992070 (p : Prop) : p = (term210 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3992071 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term156 A B f s) = (term175 A s)) = (term583 A B f s).
Proof. exact (@lem3992070 ((term156 A B f s) = (term175 A s))). Qed.
Lemma lem3992072 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term583 A B f s) = ((term156 A B f s) = (term175 A s)).
Proof. exact (SYM (@lem3992071 A B f s)). Qed.
Lemma lem3992073 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) : term584 A B f s.
Proof. exact (h1). Qed.
Lemma lem3992074 {A : Type'} : term213 A.
Proof. exact (@lem3205665 A). Qed.
Lemma lem3992076 {B : Type'} : term213 B.
Proof. exact (@lem3205665 B). Qed.
Lemma lem3992078 : term214.
Proof. exact (@lem3205665 nat). Qed.
Lemma lem3992081 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term585 A B x f s) : term585 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3992082 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term586 A B x f s.
Proof. exact (fun h0 : term585 A B x f s => @lem3992081 A B x f s h0). Qed.
Lemma lem3992083 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term586 A B x f s) : term586 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3992084 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term585 A B x f s) : term585 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3992085 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term585 A B x f s) (h2 : term586 A B x f s) : term585 A B x f s.
Proof. exact (@lem3992083 A B x f s h2 (@lem3992084 A B x f s h1)). Qed.
Lemma lem3992086 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term585 A B x f s) : term587 A B x f s.
Proof. exact (fun h0 : term586 A B x f s => @lem3992085 A B x f s h1 h0). Qed.
Lemma lem3992087 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term586 A B x f s) : term586 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3992088 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term585 A B x f s) (h2 : term586 A B x f s) : term585 A B x f s.
Proof. exact (@lem3992086 A B x f s h1 (@lem3992087 A B x f s h2)). Qed.
Lemma lem3992089 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term586 A B x f s) : term586 A B x f s.
Proof. exact (fun h0 : term585 A B x f s => @lem3992088 A B x f s h0 h1). Qed.
Lemma lem3992090 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term588 A B x f s.
Proof. exact (fun h0 : term586 A B x f s => @lem3992089 A B x f s h0). Qed.
Lemma lem3992093 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term586 A B x f s.
Proof. exact (@lem3992090 A B x f s (@lem3992082 A B x f s)). Qed.
Lemma lem3992094 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term586 A B x f s.
Proof. exact (@lem3992093 A B x f s). Qed.
Lemma lem3992232 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3992233 : term219 = term220.
Proof. exact (@lem3992232 term214). Qed.
Lemma lem3992248 {B : Type'} : (term221 B) = (term221 B).
Proof. exact (eq_refl (term221 B)). Qed.
Lemma lem3992249 {B : Type'} : (term222 B) = (term223 B).
Proof. exact (MK_COMB (@lem3992248 B) (@lem3992233)). Qed.
Lemma lem3992252 {A : Type'} : (term221 A) = (term221 A).
Proof. exact (eq_refl (term221 A)). Qed.
Lemma lem3992253 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem3992252 A) (@lem3992249 B)). Qed.
Lemma lem3992256 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term589 A B f s) = (term589 A B f s).
Proof. exact (eq_refl (term589 A B f s)). Qed.
Lemma lem3992257 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term590 A B f s) = (term591 A B f s).
Proof. exact (MK_COMB (@lem3992256 A B f s) (@lem3992253 A B)). Qed.
Lemma lem3992260 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term198 A B x f s) = (term198 A B x f s).
Proof. exact (eq_refl (term198 A B x f s)). Qed.
Lemma lem3992261 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term592 A B x f s) = (term593 A B x f s).
Proof. exact (MK_COMB (@lem3992260 A B x f s) (@lem3992257 A B f s)). Qed.
Lemma lem3992264 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term116 A B f x s) = (term116 A B f x s).
Proof. exact (eq_refl (term116 A B f x s)). Qed.
Lemma lem3992265 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term594 A B x f s) = (term595 A B x f s).
Proof. exact (MK_COMB (@lem3992264 A B f x s) (@lem3992261 A B x f s)). Qed.
Lemma lem3992268 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3992269 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term596 A B x f s) = (term597 A B x f s).
Proof. exact (MK_COMB (@lem3992268 A s) (@lem3992265 A B x f s)). Qed.
Lemma lem3992272 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem3992273 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term598 A B x f s) = (term599 A B x f s).
Proof. exact (MK_COMB (@lem3992272 A x s) (@lem3992269 A B x f s)). Qed.
Lemma lem3992276 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term238 A B f s) = (term238 A B f s).
Proof. exact (eq_refl (term238 A B f s)). Qed.
Lemma lem3992277 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term585 A B x f s) = (term600 A B x f s).
Proof. exact (MK_COMB (@lem3992276 A B f s) (@lem3992273 A B x f s)). Qed.
Lemma lem3992280 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term601 A B f s) = (term602 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992277 A B x f s)). Qed.
Lemma lem3992281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992282 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term603 A B f s) = (term604 A B f s).
Proof. exact (MK_COMB (@lem3992281 A) (@lem3992280 A B f s)). Qed.
Lemma lem3992287 {A B : Type'} (s : A -> Prop) : (term605 A B s) = (term606 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3992282 A B f s)). Qed.
Lemma lem3992288 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3992289 {A B : Type'} (s : A -> Prop) : (term607 A B s) = (term608 A B s).
Proof. exact (MK_COMB (@lem3992288 A B) (@lem3992287 A B s)). Qed.
Lemma lem3992294 {A B : Type'} : (term609 A B) = (term610 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992289 A B s)). Qed.
Lemma lem3992295 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992304 {A B : Type'} : (term611 A B) = (term612 A B).
Proof. exact (MK_COMB (@lem3992295 A) (@lem3992294 A B)). Qed.
Lemma lem3992313 (y : nat) (x : nat) (s : nat -> Prop) : ((term252 x y s) = (term253 y x s)) = ((term252 x y s) = (term253 y x s)).
Proof. exact (eq_refl ((term252 x y s) = (term253 y x s))). Qed.
Lemma lem3992314 (y : nat) (x : nat) : (term254 y x) = (term254 y x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem3992313 y x s)). Qed.
Lemma lem3992315 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem3992316 (y : nat) (x : nat) : (term255 y x) = (term255 y x).
Proof. exact (MK_COMB (@lem3992315) (@lem3992314 y x)). Qed.
Lemma lem3992317 (x : nat) : (term256 x) = (term256 x).
Proof. exact (fun_ext (fun y : nat => @lem3992316 y x)). Qed.
Lemma lem3992318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3992319 (x : nat) : (term257 x) = (term257 x).
Proof. exact (MK_COMB (@lem3992318) (@lem3992317 x)). Qed.
Lemma lem3992320 : term258 = term258.
Proof. exact (fun_ext (fun x : nat => @lem3992319 x)). Qed.
Lemma lem3992321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3992322 : term214 = term214.
Proof. exact (MK_COMB (@lem3992321) (@lem3992320)). Qed.
Lemma lem3992323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3992324 : term220 = term220.
Proof. exact (MK_COMB (@lem3992323) (@lem3992322)). Qed.
Lemma lem3992333 {B : Type'} (y : B) (x : B) (s : B -> Prop) : ((term259 B x y s) = (term260 B y x s)) = ((term259 B x y s) = (term260 B y x s)).
Proof. exact (eq_refl ((term259 B x y s) = (term260 B y x s))). Qed.
Lemma lem3992334 {B : Type'} (y : B) (x : B) : (term261 B y x) = (term261 B y x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3992333 B y x s)). Qed.
Lemma lem3992335 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3992336 {B : Type'} (y : B) (x : B) : (term262 B y x) = (term262 B y x).
Proof. exact (MK_COMB (@lem3992335 B) (@lem3992334 B y x)). Qed.
Lemma lem3992337 {B : Type'} (x : B) : (term263 B x) = (term263 B x).
Proof. exact (fun_ext (fun y : B => @lem3992336 B y x)). Qed.
Lemma lem3992338 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3992339 {B : Type'} (x : B) : (term264 B x) = (term264 B x).
Proof. exact (MK_COMB (@lem3992338 B) (@lem3992337 B x)). Qed.
Lemma lem3992340 {B : Type'} : (term265 B) = (term265 B).
Proof. exact (fun_ext (fun x : B => @lem3992339 B x)). Qed.
Lemma lem3992341 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3992342 {B : Type'} : (term213 B) = (term213 B).
Proof. exact (MK_COMB (@lem3992341 B) (@lem3992340 B)). Qed.
Lemma lem3992343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3992344 {B : Type'} : (term221 B) = (term221 B).
Proof. exact (MK_COMB (@lem3992343) (@lem3992342 B)). Qed.
Lemma lem3992345 {B : Type'} : (term223 B) = (term223 B).
Proof. exact (MK_COMB (@lem3992344 B) (@lem3992324)). Qed.
Lemma lem3992354 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term259 A x y s) = (term260 A y x s)) = ((term259 A x y s) = (term260 A y x s)).
Proof. exact (eq_refl ((term259 A x y s) = (term260 A y x s))). Qed.
Lemma lem3992355 {A : Type'} (y : A) (x : A) : (term261 A y x) = (term261 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992354 A y x s)). Qed.
Lemma lem3992356 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992357 {A : Type'} (y : A) (x : A) : (term262 A y x) = (term262 A y x).
Proof. exact (MK_COMB (@lem3992356 A) (@lem3992355 A y x)). Qed.
Lemma lem3992358 {A : Type'} (x : A) : (term263 A x) = (term263 A x).
Proof. exact (fun_ext (fun y : A => @lem3992357 A y x)). Qed.
Lemma lem3992359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992360 {A : Type'} (x : A) : (term264 A x) = (term264 A x).
Proof. exact (MK_COMB (@lem3992359 A) (@lem3992358 A x)). Qed.
Lemma lem3992361 {A : Type'} : (term265 A) = (term265 A).
Proof. exact (fun_ext (fun x : A => @lem3992360 A x)). Qed.
Lemma lem3992362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992363 {A : Type'} : (term213 A) = (term213 A).
Proof. exact (MK_COMB (@lem3992362 A) (@lem3992361 A)). Qed.
Lemma lem3992364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3992365 {A : Type'} : (term221 A) = (term221 A).
Proof. exact (MK_COMB (@lem3992364) (@lem3992363 A)). Qed.
Lemma lem3992366 {A B : Type'} : (term225 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem3992365 A) (@lem3992345 B)). Qed.
Lemma lem3992371 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term589 A B f s) = (term589 A B f s).
Proof. exact (eq_refl (term589 A B f s)). Qed.
Lemma lem3992372 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term591 A B f s) = (term591 A B f s).
Proof. exact (MK_COMB (@lem3992371 A B f s) (@lem3992366 A B)). Qed.
Lemma lem3992377 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) : (term266 A B x f x' s) = (term266 A B x f x' s).
Proof. exact (eq_refl (term266 A B x f x' s)). Qed.
Lemma lem3992378 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term267 A B x f s) = (term267 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3992377 A B x f x' s)). Qed.
Lemma lem3992379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992380 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term163 A B x f s) = (term163 A B x f s).
Proof. exact (MK_COMB (@lem3992379 A) (@lem3992378 A B x f s)). Qed.
Lemma lem3992381 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3992382 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term170 A B x f s) = (term170 A B x f s).
Proof. exact (MK_COMB (@lem3992381) (@lem3992380 A B x f s)). Qed.
Lemma lem3992383 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3992384 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term198 A B x f s) = (term198 A B x f s).
Proof. exact (MK_COMB (@lem3992383) (@lem3992382 A B x f s)). Qed.
Lemma lem3992385 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term593 A B x f s) = (term593 A B x f s).
Proof. exact (MK_COMB (@lem3992384 A B x f s) (@lem3992372 A B f s)). Qed.
Lemma lem3992398 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term268 A B f x s x' y) = (term268 A B f x s x' y).
Proof. exact (eq_refl (term268 A B f x s x' y)). Qed.
Lemma lem3992399 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term269 A B f x s x') = (term269 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3992398 A B f x s x' y)). Qed.
Lemma lem3992400 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992401 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term270 A B f x s x') = (term270 A B f x s x').
Proof. exact (MK_COMB (@lem3992400 A) (@lem3992399 A B f x s x')). Qed.
Lemma lem3992402 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term271 A B f x s) = (term271 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3992401 A B f x s x')). Qed.
Lemma lem3992403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992404 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term125 A B f x s) = (term125 A B f x s).
Proof. exact (MK_COMB (@lem3992403 A) (@lem3992402 A B f x s)). Qed.
Lemma lem3992405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3992406 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term116 A B f x s) = (term116 A B f x s).
Proof. exact (MK_COMB (@lem3992405) (@lem3992404 A B f x s)). Qed.
Lemma lem3992407 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term595 A B x f s) = (term595 A B x f s).
Proof. exact (MK_COMB (@lem3992406 A B f x s) (@lem3992385 A B x f s)). Qed.
Lemma lem3992410 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3992411 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term597 A B x f s) = (term597 A B x f s).
Proof. exact (MK_COMB (@lem3992410 A s) (@lem3992407 A B x f s)). Qed.
Lemma lem3992416 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem3992417 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term599 A B x f s) = (term599 A B x f s).
Proof. exact (MK_COMB (@lem3992416 A x s) (@lem3992411 A B x f s)). Qed.
Lemma lem3992418 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992431 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term36 A B f s x y) = (term36 A B f s x y).
Proof. exact (eq_refl (term36 A B f s x y)). Qed.
Lemma lem3992432 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term39 A B f s x) = (term39 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3992431 A B f s x y)). Qed.
Lemma lem3992433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992434 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term41 A B f s x) = (term41 A B f s x).
Proof. exact (MK_COMB (@lem3992433 A) (@lem3992432 A B f s x)). Qed.
Lemma lem3992435 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term43 A B f s) = (term43 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992434 A B f s x)). Qed.
Lemma lem3992436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992437 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term44 A B f s) = (term44 A B f s).
Proof. exact (MK_COMB (@lem3992436 A) (@lem3992435 A B f s)). Qed.
Lemma lem3992438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3992439 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term46 A B f s) = (term46 A B f s).
Proof. exact (MK_COMB (@lem3992438) (@lem3992437 A B f s)). Qed.
Lemma lem3992440 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term48 A B f s).
Proof. exact (MK_COMB (@lem3992439 A B f s) (@lem3992418 A B f s)). Qed.
Lemma lem3992441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3992442 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term238 A B f s) = (term238 A B f s).
Proof. exact (MK_COMB (@lem3992441) (@lem3992440 A B f s)). Qed.
Lemma lem3992443 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term600 A B x f s) = (term600 A B x f s).
Proof. exact (MK_COMB (@lem3992442 A B f s) (@lem3992417 A B x f s)). Qed.
Lemma lem3992444 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term602 A B f s) = (term602 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992443 A B x f s)). Qed.
Lemma lem3992445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992446 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term604 A B f s) = (term604 A B f s).
Proof. exact (MK_COMB (@lem3992445 A) (@lem3992444 A B f s)). Qed.
Lemma lem3992447 {A B : Type'} (s : A -> Prop) : (term606 A B s) = (term606 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3992446 A B f s)). Qed.
Lemma lem3992448 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3992449 {A B : Type'} (s : A -> Prop) : (term608 A B s) = (term608 A B s).
Proof. exact (MK_COMB (@lem3992448 A B) (@lem3992447 A B s)). Qed.
Lemma lem3992450 {A B : Type'} : (term610 A B) = (term610 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992449 A B s)). Qed.
Lemma lem3992451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992452 {A B : Type'} : (term612 A B) = (term612 A B).
Proof. exact (MK_COMB (@lem3992451 A) (@lem3992450 A B)). Qed.
Lemma lem3992595 {A B : Type'} : (term611 A B) = (term612 A B).
Proof. exact (TRANS (@lem3992304 A B) (@lem3992452 A B)). Qed.
Lemma lem3992596 {A B : Type'} : (term612 A B) = (term611 A B).
Proof. exact (SYM (@lem3992595 A B)). Qed.
Lemma lem3992597 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term48 A B f s.
Proof. exact (h1). Qed.
Lemma lem3992600 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term125 A B f x s.
Proof. exact (h1). Qed.
Lemma lem3992603 {A : Type'} (h1 : term213 A) : term213 A.
Proof. exact (h1). Qed.
Lemma lem3992614 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term272 A s x y) = (term273 A s x y).
Proof. exact (@lem17362 (@IN A x s) (x = y)). Qed.
Lemma lem3992616 {A : Type'} (y : A) (s : A -> Prop) : (term274 A y s) = (term274 A y s).
Proof. exact (eq_refl (term274 A y s)). Qed.
Lemma lem3992617 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term275 A s x y) = (term276 A s x y).
Proof. exact (MK_COMB (@lem3992616 A y s) (@lem3992614 A s x y)). Qed.
Lemma lem3992618 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term277 A s x y) = (term275 A s x y).
Proof. exact (@lem17362 (@IN A y s) (term37 A s x y)). Qed.
Lemma lem3992619 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term277 A s x y) = (term276 A s x y).
Proof. exact (TRANS (@lem3992618 A s x y) (@lem3992617 A s x y)). Qed.
Lemma lem3992621 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term278 A B x f y) = (term278 A B x f y).
Proof. exact (eq_refl (term278 A B x f y)). Qed.
Lemma lem3992622 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term279 A B f s x y) = (term280 A B f s x y).
Proof. exact (MK_COMB (@lem3992621 A B x f y) (@lem3992619 A s x y)). Qed.
Lemma lem3992623 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term281 A B f s x y) = (term279 A B f s x y).
Proof. exact (@lem17362 ((f x) = (f y)) (term282 A s x y)). Qed.
Lemma lem3992624 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term281 A B f s x y) = (term280 A B f s x y).
Proof. exact (TRANS (@lem3992623 A B f s x y) (@lem3992622 A B f s x y)). Qed.
Lemma lem3992625 {A : Type'} (P : A -> Prop) : (term283 A P) = (term284 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3992626 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term285 A B f s x) = (term286 A B f s x).
Proof. exact (@lem3992625 A (term39 A B f s x)). Qed.
Lemma lem3992627 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term287 A B f s x y) = (term36 A B f s x y).
Proof. exact (eq_refl (term287 A B f s x y)). Qed.
Lemma lem3992628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3992629 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term288 A B f s x y) = (term281 A B f s x y).
Proof. exact (MK_COMB (@lem3992628) (@lem3992627 A B f s x y)). Qed.
Lemma lem3992630 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term288 A B f s x y) = (term280 A B f s x y).
Proof. exact (TRANS (@lem3992629 A B f s x y) (@lem3992624 A B f s x y)). Qed.
Lemma lem3992631 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term289 A B f s x) = (term290 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3992630 A B f s x y)). Qed.
Lemma lem3992632 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992633 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term286 A B f s x) = (term291 A B f s x).
Proof. exact (MK_COMB (@lem3992632 A) (@lem3992631 A B f s x)). Qed.
Lemma lem3992634 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term285 A B f s x) = (term291 A B f s x).
Proof. exact (TRANS (@lem3992626 A B f s x) (@lem3992633 A B f s x)). Qed.
Lemma lem3992635 {A : Type'} (P : A -> Prop) : (term283 A P) = (term284 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3992636 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term292 A B f s) = (term293 A B f s).
Proof. exact (@lem3992635 A (term43 A B f s)). Qed.
Lemma lem3992637 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term294 A B f s x) = (term41 A B f s x).
Proof. exact (eq_refl (term294 A B f s x)). Qed.
Lemma lem3992638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3992639 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term295 A B f s x) = (term285 A B f s x).
Proof. exact (MK_COMB (@lem3992638) (@lem3992637 A B f s x)). Qed.
Lemma lem3992640 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term295 A B f s x) = (term291 A B f s x).
Proof. exact (TRANS (@lem3992639 A B f s x) (@lem3992634 A B f s x)). Qed.
Lemma lem3992641 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term296 A B f s) = (term297 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992640 A B f s x)). Qed.
Lemma lem3992642 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992643 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term293 A B f s) = (term298 A B f s).
Proof. exact (MK_COMB (@lem3992642 A) (@lem3992641 A B f s)). Qed.
Lemma lem3992644 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term292 A B f s) = (term298 A B f s).
Proof. exact (TRANS (@lem3992636 A B f s) (@lem3992643 A B f s)). Qed.
Lemma lem3992645 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3992647 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term299 A B f s) = (term300 A B f s).
Proof. exact (MK_COMB (@lem3992646) (@lem3992644 A B f s)). Qed.
Lemma lem3992648 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term301 A B f s) = (term302 A B f s).
Proof. exact (MK_COMB (@lem3992647 A B f s) (@lem3992645 A B f s)). Qed.
Lemma lem3992649 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term301 A B f s).
Proof. exact (@lem17265 (term44 A B f s) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992650 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term302 A B f s).
Proof. exact (TRANS (@lem3992649 A B f s) (@lem3992648 A B f s)). Qed.
Lemma lem3992705 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3992706 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem3992705 A P Q). Qed.
Lemma lem3992707 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term305 A B f s) = (term306 A B f s).
Proof. exact (@lem3992706 A (term297 A B f s) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992708 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term307 A B f s x) = (term291 A B f s x).
Proof. exact (eq_refl (term307 A B f s x)). Qed.
Lemma lem3992709 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term308 A B f s) = (term297 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992708 A B f s x)). Qed.
Lemma lem3992710 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992711 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term309 A B f s) = (term298 A B f s).
Proof. exact (MK_COMB (@lem3992710 A) (@lem3992709 A B f s)). Qed.
Lemma lem3992712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3992713 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term310 A B f s) = (term300 A B f s).
Proof. exact (MK_COMB (@lem3992712) (@lem3992711 A B f s)). Qed.
Lemma lem3992714 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992715 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term305 A B f s) = (term302 A B f s).
Proof. exact (MK_COMB (@lem3992713 A B f s) (@lem3992714 A B f s)). Qed.
Lemma lem3992716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3992717 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term311 A B f s) = (term312 A B f s).
Proof. exact (MK_COMB (@lem3992716) (@lem3992715 A B f s)). Qed.
Lemma lem3992718 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term307 A B f s x) = (term291 A B f s x).
Proof. exact (eq_refl (term307 A B f s x)). Qed.
Lemma lem3992719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3992720 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term313 A B f s x) = (term314 A B f s x).
Proof. exact (MK_COMB (@lem3992719) (@lem3992718 A B f s x)). Qed.
Lemma lem3992721 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992722 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term315 A B x f s) = (term316 A B x f s).
Proof. exact (MK_COMB (@lem3992720 A B f s x) (@lem3992721 A B f s)). Qed.
Lemma lem3992723 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term317 A B f s) = (term318 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992722 A B x f s)). Qed.
Lemma lem3992724 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992725 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term306 A B f s) = (term319 A B f s).
Proof. exact (MK_COMB (@lem3992724 A) (@lem3992723 A B f s)). Qed.
Lemma lem3992726 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term305 A B f s) = (term306 A B f s)) = ((term302 A B f s) = (term319 A B f s)).
Proof. exact (MK_COMB (@lem3992717 A B f s) (@lem3992725 A B f s)). Qed.
Lemma lem3992727 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term302 A B f s) = (term319 A B f s).
Proof. exact (EQ_MP (@lem3992726 A B f s) (@lem3992707 A B f s)). Qed.
Lemma lem3992729 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3992730 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem3992729 A P Q). Qed.
Lemma lem3992731 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term320 A B x f s) = (term321 A B x f s).
Proof. exact (@lem3992730 A (term290 A B f s x) ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992732 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term322 A B f s x y) = (term280 A B f s x y).
Proof. exact (eq_refl (term322 A B f s x y)). Qed.
Lemma lem3992733 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term323 A B f s x) = (term290 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem3992732 A B f s x y)). Qed.
Lemma lem3992734 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992735 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term324 A B f s x) = (term291 A B f s x).
Proof. exact (MK_COMB (@lem3992734 A) (@lem3992733 A B f s x)). Qed.
Lemma lem3992736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3992737 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term325 A B f s x) = (term314 A B f s x).
Proof. exact (MK_COMB (@lem3992736) (@lem3992735 A B f s x)). Qed.
Lemma lem3992738 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992739 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term320 A B x f s) = (term316 A B x f s).
Proof. exact (MK_COMB (@lem3992737 A B f s x) (@lem3992738 A B f s)). Qed.
Lemma lem3992740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3992741 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term326 A B x f s) = (term327 A B x f s).
Proof. exact (MK_COMB (@lem3992740) (@lem3992739 A B x f s)). Qed.
Lemma lem3992742 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term322 A B f s x y) = (term280 A B f s x y).
Proof. exact (eq_refl (term322 A B f s x y)). Qed.
Lemma lem3992743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3992744 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term328 A B f s x y) = (term329 A B f s x y).
Proof. exact (MK_COMB (@lem3992743) (@lem3992742 A B f s x y)). Qed.
Lemma lem3992745 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3992746 {A B : Type'} (x : A) (y : A) (f : A -> B) (s : A -> Prop) : (term330 A B x y f s) = (term331 A B x y f s).
Proof. exact (MK_COMB (@lem3992744 A B f s x y) (@lem3992745 A B f s)). Qed.
Lemma lem3992747 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term332 A B x f s) = (term333 A B x f s).
Proof. exact (fun_ext (fun y : A => @lem3992746 A B x y f s)). Qed.
Lemma lem3992748 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992749 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term334 A B x f s).
Proof. exact (MK_COMB (@lem3992748 A) (@lem3992747 A B x f s)). Qed.
Lemma lem3992750 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term320 A B x f s) = (term321 A B x f s)) = ((term316 A B x f s) = (term334 A B x f s)).
Proof. exact (MK_COMB (@lem3992741 A B x f s) (@lem3992749 A B x f s)). Qed.
Lemma lem3992751 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term316 A B x f s) = (term334 A B x f s).
Proof. exact (EQ_MP (@lem3992750 A B x f s) (@lem3992731 A B x f s)). Qed.
Lemma lem3992752 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term318 A B f s) = (term335 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3992751 A B x f s)). Qed.
Lemma lem3992753 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3992754 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term319 A B f s) = (term336 A B f s).
Proof. exact (MK_COMB (@lem3992753 A) (@lem3992752 A B f s)). Qed.
Lemma lem3992756 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term302 A B f s) = (term336 A B f s).
Proof. exact (TRANS (@lem3992727 A B f s) (@lem3992754 A B f s)). Qed.
Lemma lem3992757 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term336 A B f s).
Proof. exact (TRANS (@lem3992650 A B f s) (@lem3992756 A B f s)). Qed.
Lemma lem3992758 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term336 A B f s.
Proof. exact (EQ_MP (@lem3992757 A B f s) (@lem3992597 A B f s h1)). Qed.
Lemma lem3992779 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term337 A x s x' y) = (term338 A x s x' y).
Proof. exact (@lem17265 (term259 A x' x s) (x' = y)). Qed.
Lemma lem3992781 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term339 A y x s) = (term339 A y x s).
Proof. exact (eq_refl (term339 A y x s)). Qed.
Lemma lem3992782 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term340 A x s x' y) = (term341 A x s x' y).
Proof. exact (MK_COMB (@lem3992781 A y x s) (@lem3992779 A x s x' y)). Qed.
Lemma lem3992783 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term342 A x s x' y) = (term340 A x s x' y).
Proof. exact (@lem17265 (term259 A y x s) (term337 A x s x' y)). Qed.
Lemma lem3992784 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term342 A x s x' y) = (term341 A x s x' y).
Proof. exact (TRANS (@lem3992783 A x s x' y) (@lem3992782 A x s x' y)). Qed.
Lemma lem3992786 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term343 A B x' f y) = (term343 A B x' f y).
Proof. exact (eq_refl (term343 A B x' f y)). Qed.
Lemma lem3992787 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term344 A B f x s x' y) = (term345 A B f x s x' y).
Proof. exact (MK_COMB (@lem3992786 A B x' f y) (@lem3992784 A x s x' y)). Qed.
Lemma lem3992788 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term268 A B f x s x' y) = (term344 A B f x s x' y).
Proof. exact (@lem17265 ((f x') = (f y)) (term342 A x s x' y)). Qed.
Lemma lem3992789 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term268 A B f x s x' y) = (term345 A B f x s x' y).
Proof. exact (TRANS (@lem3992788 A B f x s x' y) (@lem3992787 A B f x s x' y)). Qed.
Lemma lem3992790 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term269 A B f x s x') = (term346 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3992789 A B f x s x' y)). Qed.
Lemma lem3992791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992792 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term270 A B f x s x') = (term347 A B f x s x').
Proof. exact (MK_COMB (@lem3992791 A) (@lem3992790 A B f x s x')). Qed.
Lemma lem3992793 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term271 A B f x s) = (term348 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3992792 A B f x s x')). Qed.
Lemma lem3992794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992851 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term125 A B f x s) = (term349 A B f x s).
Proof. exact (MK_COMB (@lem3992794 A) (@lem3992793 A B f x s)). Qed.
Lemma lem3992852 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term349 A B f x s.
Proof. exact (EQ_MP (@lem3992851 A B f x s) (@lem3992600 A B f x s h1)). Qed.
Lemma lem3992928 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) : term584 A B f s.
Proof. exact (h1). Qed.
Lemma lem3992939 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term350 A y x s) = (term351 A y x s).
Proof. exact (@lem17160 (x = y) (@IN A x s)). Qed.
Lemma lem3992945 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term352 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term352 A y x s)). Qed.
Lemma lem3992947 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term353 A x y s) = (term353 A x y s).
Proof. exact (eq_refl (term353 A x y s)). Qed.
Lemma lem3992948 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term354 A y x s) = (term355 A y x s).
Proof. exact (MK_COMB (@lem3992947 A x y s) (@lem3992939 A y x s)). Qed.
Lemma lem3992949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3992950 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term356 A y x s) = (term357 A y x s).
Proof. exact (MK_COMB (@lem3992949) (@lem3992948 A y x s)). Qed.
Lemma lem3992951 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term358 A y x s) = (term359 A y x s).
Proof. exact (MK_COMB (@lem3992950 A y x s) (@lem3992945 A y x s)). Qed.
Lemma lem3992952 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term259 A x y s) = (term260 A y x s)) = (term358 A y x s).
Proof. exact (@lem17784 (term259 A x y s) (term260 A y x s)). Qed.
Lemma lem3992953 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term259 A x y s) = (term260 A y x s)) = (term359 A y x s).
Proof. exact (TRANS (@lem3992952 A y x s) (@lem3992951 A y x s)). Qed.
Lemma lem3992954 {A : Type'} (y : A) (x : A) : (term261 A y x) = (term360 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992953 A y x s)). Qed.
Lemma lem3992955 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992956 {A : Type'} (y : A) (x : A) : (term262 A y x) = (term361 A y x).
Proof. exact (MK_COMB (@lem3992955 A) (@lem3992954 A y x)). Qed.
Lemma lem3992957 {A : Type'} (x : A) : (term263 A x) = (term362 A x).
Proof. exact (fun_ext (fun y : A => @lem3992956 A y x)). Qed.
Lemma lem3992958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992959 {A : Type'} (x : A) : (term264 A x) = (term363 A x).
Proof. exact (MK_COMB (@lem3992958 A) (@lem3992957 A x)). Qed.
Lemma lem3992960 {A : Type'} : (term265 A) = (term364 A).
Proof. exact (fun_ext (fun x : A => @lem3992959 A x)). Qed.
Lemma lem3992961 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3992962 {A : Type'} : (term213 A) = (term365 A).
Proof. exact (MK_COMB (@lem3992961 A) (@lem3992960 A)). Qed.
Lemma lem3992972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3992973 {A : Type'} (P : type686 A) (Q : type686 A) : (term368 A P Q) = (term369 A P Q).
Proof. exact (@lem3992972 (A -> Prop) P Q). Qed.
Lemma lem3992974 {A : Type'} (y : A) (x : A) : (term370 A y x) = (term371 A y x).
Proof. exact (@lem3992973 A (term372 A y x) (term373 A y x)). Qed.
Lemma lem3992975 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term374 A y x s) = (term355 A y x s).
Proof. exact (eq_refl (term374 A y x s)). Qed.
Lemma lem3992976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3992977 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term375 A y x s) = (term357 A y x s).
Proof. exact (MK_COMB (@lem3992976) (@lem3992975 A y x s)). Qed.
Lemma lem3992978 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term376 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term376 A y x s)). Qed.
Lemma lem3992979 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term377 A y x s) = (term359 A y x s).
Proof. exact (MK_COMB (@lem3992977 A y x s) (@lem3992978 A y x s)). Qed.
Lemma lem3992980 {A : Type'} (y : A) (x : A) : (term378 A y x) = (term360 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992979 A y x s)). Qed.
Lemma lem3992981 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992982 {A : Type'} (y : A) (x : A) : (term370 A y x) = (term361 A y x).
Proof. exact (MK_COMB (@lem3992981 A) (@lem3992980 A y x)). Qed.
Lemma lem3992983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3992984 {A : Type'} (y : A) (x : A) : (term379 A y x) = (term380 A y x).
Proof. exact (MK_COMB (@lem3992983) (@lem3992982 A y x)). Qed.
Lemma lem3992985 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term374 A y x s) = (term355 A y x s).
Proof. exact (eq_refl (term374 A y x s)). Qed.
Lemma lem3992986 {A : Type'} (y : A) (x : A) : (term381 A y x) = (term372 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992985 A y x s)). Qed.
Lemma lem3992987 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992988 {A : Type'} (y : A) (x : A) : (term382 A y x) = (term383 A y x).
Proof. exact (MK_COMB (@lem3992987 A) (@lem3992986 A y x)). Qed.
Lemma lem3992989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3992990 {A : Type'} (y : A) (x : A) : (term384 A y x) = (term385 A y x).
Proof. exact (MK_COMB (@lem3992989) (@lem3992988 A y x)). Qed.
Lemma lem3992991 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term376 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term376 A y x s)). Qed.
Lemma lem3992992 {A : Type'} (y : A) (x : A) : (term386 A y x) = (term373 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3992991 A y x s)). Qed.
Lemma lem3992993 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3992994 {A : Type'} (y : A) (x : A) : (term387 A y x) = (term388 A y x).
Proof. exact (MK_COMB (@lem3992993 A) (@lem3992992 A y x)). Qed.
Lemma lem3992995 {A : Type'} (y : A) (x : A) : (term371 A y x) = (term389 A y x).
Proof. exact (MK_COMB (@lem3992990 A y x) (@lem3992994 A y x)). Qed.
Lemma lem3992996 {A : Type'} (y : A) (x : A) : ((term370 A y x) = (term371 A y x)) = ((term361 A y x) = (term389 A y x)).
Proof. exact (MK_COMB (@lem3992984 A y x) (@lem3992995 A y x)). Qed.
Lemma lem3992997 {A : Type'} (y : A) (x : A) : (term361 A y x) = (term389 A y x).
Proof. exact (EQ_MP (@lem3992996 A y x) (@lem3992974 A y x)). Qed.
Lemma lem3993094 {A : Type'} (x : A) : (term362 A x) = (term390 A x).
Proof. exact (fun_ext (fun y : A => @lem3992997 A y x)). Qed.
Lemma lem3993095 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993096 {A : Type'} (x : A) : (term363 A x) = (term391 A x).
Proof. exact (MK_COMB (@lem3993095 A) (@lem3993094 A x)). Qed.
Lemma lem3993098 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3993099 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (@lem3993098 A P Q). Qed.
Lemma lem3993100 {A : Type'} (x : A) : (term392 A x) = (term393 A x).
Proof. exact (@lem3993099 A (term394 A x) (term395 A x)). Qed.
Lemma lem3993101 {A : Type'} (y : A) (x : A) : (term396 A x y) = (term383 A y x).
Proof. exact (eq_refl (term396 A x y)). Qed.
Lemma lem3993102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3993103 {A : Type'} (y : A) (x : A) : (term397 A x y) = (term385 A y x).
Proof. exact (MK_COMB (@lem3993102) (@lem3993101 A y x)). Qed.
Lemma lem3993104 {A : Type'} (y : A) (x : A) : (term398 A x y) = (term388 A y x).
Proof. exact (eq_refl (term398 A x y)). Qed.
Lemma lem3993105 {A : Type'} (y : A) (x : A) : (term399 A x y) = (term389 A y x).
Proof. exact (MK_COMB (@lem3993103 A y x) (@lem3993104 A y x)). Qed.
Lemma lem3993106 {A : Type'} (x : A) : (term400 A x) = (term390 A x).
Proof. exact (fun_ext (fun y : A => @lem3993105 A y x)). Qed.
Lemma lem3993107 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993108 {A : Type'} (x : A) : (term392 A x) = (term391 A x).
Proof. exact (MK_COMB (@lem3993107 A) (@lem3993106 A x)). Qed.
Lemma lem3993109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3993110 {A : Type'} (x : A) : (term401 A x) = (term402 A x).
Proof. exact (MK_COMB (@lem3993109) (@lem3993108 A x)). Qed.
Lemma lem3993111 {A : Type'} (y : A) (x : A) : (term396 A x y) = (term383 A y x).
Proof. exact (eq_refl (term396 A x y)). Qed.
Lemma lem3993112 {A : Type'} (x : A) : (term403 A x) = (term394 A x).
Proof. exact (fun_ext (fun y : A => @lem3993111 A y x)). Qed.
Lemma lem3993113 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993114 {A : Type'} (x : A) : (term404 A x) = (term405 A x).
Proof. exact (MK_COMB (@lem3993113 A) (@lem3993112 A x)). Qed.
Lemma lem3993115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3993116 {A : Type'} (x : A) : (term406 A x) = (term407 A x).
Proof. exact (MK_COMB (@lem3993115) (@lem3993114 A x)). Qed.
Lemma lem3993117 {A : Type'} (y : A) (x : A) : (term398 A x y) = (term388 A y x).
Proof. exact (eq_refl (term398 A x y)). Qed.
Lemma lem3993118 {A : Type'} (x : A) : (term408 A x) = (term395 A x).
Proof. exact (fun_ext (fun y : A => @lem3993117 A y x)). Qed.
Lemma lem3993119 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993120 {A : Type'} (x : A) : (term409 A x) = (term410 A x).
Proof. exact (MK_COMB (@lem3993119 A) (@lem3993118 A x)). Qed.
Lemma lem3993121 {A : Type'} (x : A) : (term393 A x) = (term411 A x).
Proof. exact (MK_COMB (@lem3993116 A x) (@lem3993120 A x)). Qed.
Lemma lem3993122 {A : Type'} (x : A) : ((term392 A x) = (term393 A x)) = ((term391 A x) = (term411 A x)).
Proof. exact (MK_COMB (@lem3993110 A x) (@lem3993121 A x)). Qed.
Lemma lem3993123 {A : Type'} (x : A) : (term391 A x) = (term411 A x).
Proof. exact (EQ_MP (@lem3993122 A x) (@lem3993100 A x)). Qed.
Lemma lem3993228 {A : Type'} (x : A) : (term363 A x) = (term411 A x).
Proof. exact (TRANS (@lem3993096 A x) (@lem3993123 A x)). Qed.
Lemma lem3993229 {A : Type'} : (term364 A) = (term412 A).
Proof. exact (fun_ext (fun x : A => @lem3993228 A x)). Qed.
Lemma lem3993230 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993231 {A : Type'} : (term365 A) = (term413 A).
Proof. exact (MK_COMB (@lem3993230 A) (@lem3993229 A)). Qed.
Lemma lem3993233 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3993234 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term366 A P Q) = (term367 A P Q).
Proof. exact (@lem3993233 A P Q). Qed.
Lemma lem3993235 {A : Type'} : (term414 A) = (term415 A).
Proof. exact (@lem3993234 A (term416 A) (term417 A)). Qed.
Lemma lem3993236 {A : Type'} (x : A) : (term418 A x) = (term405 A x).
Proof. exact (eq_refl (term418 A x)). Qed.
Lemma lem3993237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3993238 {A : Type'} (x : A) : (term419 A x) = (term407 A x).
Proof. exact (MK_COMB (@lem3993237) (@lem3993236 A x)). Qed.
Lemma lem3993239 {A : Type'} (x : A) : (term420 A x) = (term410 A x).
Proof. exact (eq_refl (term420 A x)). Qed.
Lemma lem3993240 {A : Type'} (x : A) : (term421 A x) = (term411 A x).
Proof. exact (MK_COMB (@lem3993238 A x) (@lem3993239 A x)). Qed.
Lemma lem3993241 {A : Type'} : (term422 A) = (term412 A).
Proof. exact (fun_ext (fun x : A => @lem3993240 A x)). Qed.
Lemma lem3993242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993243 {A : Type'} : (term414 A) = (term413 A).
Proof. exact (MK_COMB (@lem3993242 A) (@lem3993241 A)). Qed.
Lemma lem3993244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3993245 {A : Type'} : (term423 A) = (term424 A).
Proof. exact (MK_COMB (@lem3993244) (@lem3993243 A)). Qed.
Lemma lem3993246 {A : Type'} (x : A) : (term418 A x) = (term405 A x).
Proof. exact (eq_refl (term418 A x)). Qed.
Lemma lem3993247 {A : Type'} : (term425 A) = (term416 A).
Proof. exact (fun_ext (fun x : A => @lem3993246 A x)). Qed.
Lemma lem3993248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993249 {A : Type'} : (term426 A) = (term427 A).
Proof. exact (MK_COMB (@lem3993248 A) (@lem3993247 A)). Qed.
Lemma lem3993250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3993251 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (MK_COMB (@lem3993250) (@lem3993249 A)). Qed.
Lemma lem3993252 {A : Type'} (x : A) : (term420 A x) = (term410 A x).
Proof. exact (eq_refl (term420 A x)). Qed.
Lemma lem3993253 {A : Type'} : (term430 A) = (term417 A).
Proof. exact (fun_ext (fun x : A => @lem3993252 A x)). Qed.
Lemma lem3993254 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3993255 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (MK_COMB (@lem3993254 A) (@lem3993253 A)). Qed.
Lemma lem3993256 {A : Type'} : (term415 A) = (term433 A).
Proof. exact (MK_COMB (@lem3993251 A) (@lem3993255 A)). Qed.
Lemma lem3993257 {A : Type'} : ((term414 A) = (term415 A)) = ((term413 A) = (term433 A)).
Proof. exact (MK_COMB (@lem3993245 A) (@lem3993256 A)). Qed.
Lemma lem3993258 {A : Type'} : (term413 A) = (term433 A).
Proof. exact (EQ_MP (@lem3993257 A) (@lem3993235 A)). Qed.
Lemma lem3993373 {A : Type'} : (term365 A) = (term433 A).
Proof. exact (TRANS (@lem3993231 A) (@lem3993258 A)). Qed.
Lemma lem3993374 {A : Type'} : (term213 A) = (term433 A).
Proof. exact (TRANS (@lem3992962 A) (@lem3993373 A)). Qed.
Lemma lem3993375 {A : Type'} (h1 : term213 A) : term433 A.
Proof. exact (EQ_MP (@lem3993374 A) (@lem3992603 A h1)). Qed.
Lemma lem3994270 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (h1 : term334 A B x' f s) : term334 A B x' f s.
Proof. exact (h1). Qed.
Lemma lem3994271 {A B : Type'} (x' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term331 A B x' y f s) : term331 A B x' y f s.
Proof. exact (h1). Qed.
Lemma lem3994316 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term341 A x s x' y) = (term341 A x s x' y).
Proof. exact (eq_refl (term341 A x s x' y)). Qed.
Lemma lem3994317 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3994318 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3994323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3994324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3994323 A B f x). Qed.
Lemma lem3994326 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem3994324 A B f x'). Qed.
Lemma lem3994331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3994332 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3994331 A B f x). Qed.
Lemma lem3994334 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3994332 A B f y). Qed.
Lemma lem3994335 {A B : Type'} (f : A -> B) (x' : A) : (term434 A B f x') = (term435 A B f x').
Proof. exact (MK_COMB (@lem3994318 B) (@lem3994326 A B f x')). Qed.
Lemma lem3994336 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3994335 A B f x') (@lem3994334 A B f y)). Qed.
Lemma lem3994337 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term436 A B x' f y) = (term437 A B x' f y).
Proof. exact (MK_COMB (@lem3994317) (@lem3994336 A B x' f y)). Qed.
Lemma lem3994338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3994339 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term343 A B x' f y) = (term438 A B x' f y).
Proof. exact (MK_COMB (@lem3994338) (@lem3994337 A B x' f y)). Qed.
Lemma lem3994340 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term345 A B f x s x' y) = (term439 A B f x s x' y).
Proof. exact (MK_COMB (@lem3994339 A B x' f y) (@lem3994316 A x s x' y)). Qed.
Lemma lem3994341 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term346 A B f x s x') = (term440 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3994340 A B f x s x' y)). Qed.
Lemma lem3994342 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994343 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term347 A B f x s x') = (term441 A B f x s x').
Proof. exact (MK_COMB (@lem3994342 A) (@lem3994341 A B f x s x')). Qed.
Lemma lem3994344 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term348 A B f x s) = (term442 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3994343 A B f x s x')). Qed.
Lemma lem3994345 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994346 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term349 A B f x s) = (term443 A B f x s).
Proof. exact (MK_COMB (@lem3994345 A) (@lem3994344 A B f x s)). Qed.
Lemma lem3994347 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term443 A B f x s.
Proof. exact (EQ_MP (@lem3994346 A B f x s) (@lem3992852 A B f x s h1)). Qed.
Lemma lem3994401 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) : term584 A B f s.
Proof. exact (h1). Qed.
Lemma lem3994428 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term352 A y x s) = (term352 A y x s).
Proof. exact (eq_refl (term352 A y x s)). Qed.
Lemma lem3994429 {A : Type'} (y : A) (x : A) : (term373 A y x) = (term373 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3994428 A y x s)). Qed.
Lemma lem3994430 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3994431 {A : Type'} (y : A) (x : A) : (term388 A y x) = (term388 A y x).
Proof. exact (MK_COMB (@lem3994430 A) (@lem3994429 A y x)). Qed.
Lemma lem3994432 {A : Type'} (x : A) : (term395 A x) = (term395 A x).
Proof. exact (fun_ext (fun y : A => @lem3994431 A y x)). Qed.
Lemma lem3994433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994434 {A : Type'} (x : A) : (term410 A x) = (term410 A x).
Proof. exact (MK_COMB (@lem3994433 A) (@lem3994432 A x)). Qed.
Lemma lem3994435 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (fun_ext (fun x : A => @lem3994434 A x)). Qed.
Lemma lem3994436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994437 {A : Type'} : (term432 A) = (term432 A).
Proof. exact (MK_COMB (@lem3994436 A) (@lem3994435 A)). Qed.
Lemma lem3994466 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term355 A y x s) = (term355 A y x s).
Proof. exact (eq_refl (term355 A y x s)). Qed.
Lemma lem3994467 {A : Type'} (y : A) (x : A) : (term372 A y x) = (term372 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3994466 A y x s)). Qed.
Lemma lem3994468 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3994469 {A : Type'} (y : A) (x : A) : (term383 A y x) = (term383 A y x).
Proof. exact (MK_COMB (@lem3994468 A) (@lem3994467 A y x)). Qed.
Lemma lem3994470 {A : Type'} (x : A) : (term394 A x) = (term394 A x).
Proof. exact (fun_ext (fun y : A => @lem3994469 A y x)). Qed.
Lemma lem3994471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994472 {A : Type'} (x : A) : (term405 A x) = (term405 A x).
Proof. exact (MK_COMB (@lem3994471 A) (@lem3994470 A x)). Qed.
Lemma lem3994473 {A : Type'} : (term416 A) = (term416 A).
Proof. exact (fun_ext (fun x : A => @lem3994472 A x)). Qed.
Lemma lem3994474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994475 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem3994474 A) (@lem3994473 A)). Qed.
Lemma lem3994476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3994477 {A : Type'} : (term429 A) = (term429 A).
Proof. exact (MK_COMB (@lem3994476) (@lem3994475 A)). Qed.
Lemma lem3994478 {A : Type'} : (term433 A) = (term433 A).
Proof. exact (MK_COMB (@lem3994477 A) (@lem3994437 A)). Qed.
Lemma lem3994479 {A : Type'} (h1 : term213 A) : term433 A.
Proof. exact (EQ_MP (@lem3994478 A) (@lem3993375 A h1)). Qed.
Lemma lem3994648 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term32 A B f s) = (@CARD A s)) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3994671 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term276 A s x' y) = (term276 A s x' y).
Proof. exact (eq_refl (term276 A s x' y)). Qed.
Lemma lem3994672 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3994677 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3994678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3994677 A B f x). Qed.
Lemma lem3994680 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem3994678 A B f x'). Qed.
Lemma lem3994685 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3994686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3994685 A B f x). Qed.
Lemma lem3994688 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3994686 A B f y). Qed.
Lemma lem3994689 {A B : Type'} (f : A -> B) (x' : A) : (term434 A B f x') = (term435 A B f x').
Proof. exact (MK_COMB (@lem3994672 B) (@lem3994680 A B f x')). Qed.
Lemma lem3994690 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3994689 A B f x') (@lem3994688 A B f y)). Qed.
Lemma lem3994691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3994692 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term278 A B x' f y) = (term444 A B x' f y).
Proof. exact (MK_COMB (@lem3994691) (@lem3994690 A B x' f y)). Qed.
Lemma lem3994693 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) : (term280 A B f s x' y) = (term446 A B f s x' y).
Proof. exact (MK_COMB (@lem3994692 A B x' f y) (@lem3994671 A s x' y)). Qed.
Lemma lem3994694 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3994695 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) : (term329 A B f s x' y) = (term447 A B f s x' y).
Proof. exact (MK_COMB (@lem3994694) (@lem3994693 A B f s x' y)). Qed.
Lemma lem3994696 {A B : Type'} (x' : A) (y : A) (f : A -> B) (s : A -> Prop) : (term331 A B x' y f s) = (term448 A B x' y f s).
Proof. exact (MK_COMB (@lem3994695 A B f s x' y) (@lem3994648 A B f s)). Qed.
Lemma lem3994697 {A B : Type'} (x' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term331 A B x' y f s) : term448 A B x' y f s.
Proof. exact (EQ_MP (@lem3994696 A B x' y f s) (@lem3994271 A B x' y f s h1)). Qed.
Lemma lem3994703 {A : Type'} (h1 : term213 A) : term427 A.
Proof. exact (proj1 (@lem3994479 A h1)). Qed.
Lemma lem3994704 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term446 A B f s x' y.
Proof. exact (h1). Qed.
Lemma lem3994706 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term276 A s x' y.
Proof. exact (proj2 (@lem3994704 A B f s x' y h1)). Qed.
Lemma lem3994708 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term273 A s x' y.
Proof. exact (proj2 (@lem3994706 A B f s x' y h1)). Qed.
Lemma lem3994739 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) (y : A) : (term439 A B f x s x' y) = (term439 A B f x s x' y).
Proof. exact (eq_refl (term439 A B f x s x' y)). Qed.
Lemma lem3994740 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term440 A B f x s x') = (term440 A B f x s x').
Proof. exact (fun_ext (fun y : A => @lem3994739 A B f x s x' y)). Qed.
Lemma lem3994741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994742 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (x' : A) : (term441 A B f x s x') = (term441 A B f x s x').
Proof. exact (MK_COMB (@lem3994741 A) (@lem3994740 A B f x s x')). Qed.
Lemma lem3994743 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term442 A B f x s) = (term442 A B f x s).
Proof. exact (fun_ext (fun x' : A => @lem3994742 A B f x s x')). Qed.
Lemma lem3994744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994746 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term443 A B f x s) = (term443 A B f x s).
Proof. exact (MK_COMB (@lem3994744 A) (@lem3994743 A B f x s)). Qed.
Lemma lem3994747 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term443 A B f x s.
Proof. exact (EQ_MP (@lem3994746 A B f x s) (@lem3994347 A B f x s h1)). Qed.
Lemma lem3994890 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term355 A y x s) = (term449 A y x s).
Proof. exact (@lem19490 (term450 A x y) (term259 A x y s) (term124 A x s)). Qed.
Lemma lem3994891 {A : Type'} (y : A) (x : A) : (term372 A y x) = (term451 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3994890 A y x s)). Qed.
Lemma lem3994892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3994893 {A : Type'} (y : A) (x : A) : (term383 A y x) = (term452 A y x).
Proof. exact (MK_COMB (@lem3994892 A) (@lem3994891 A y x)). Qed.
Lemma lem3994894 {A : Type'} (x : A) : (term394 A x) = (term453 A x).
Proof. exact (fun_ext (fun y : A => @lem3994893 A y x)). Qed.
Lemma lem3994895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994896 {A : Type'} (x : A) : (term405 A x) = (term454 A x).
Proof. exact (MK_COMB (@lem3994895 A) (@lem3994894 A x)). Qed.
Lemma lem3994897 {A : Type'} : (term416 A) = (term455 A).
Proof. exact (fun_ext (fun x : A => @lem3994896 A x)). Qed.
Lemma lem3994898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3994900 {A : Type'} : (term427 A) = (term456 A).
Proof. exact (MK_COMB (@lem3994898 A) (@lem3994897 A)). Qed.
Lemma lem3994901 {A : Type'} (h1 : term213 A) : term456 A.
Proof. exact (EQ_MP (@lem3994900 A) (@lem3994703 A h1)). Qed.
Lemma lem3994995 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) : term584 A B f s.
Proof. exact (h1). Qed.
Lemma lem3995161 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : (term32 A B f s) = (@CARD A s).
Proof. exact (h1). Qed.
Lemma lem3995162 {A B : Type'} (_45950 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term457 A B f x s _45950.
Proof. exact (@lem3994747 A B f x s h1 _45950). Qed.
Lemma lem3995163 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45950 : A) : (term457 A B f x s _45950) = (term441 A B f x s _45950).
Proof. exact (eq_refl (term457 A B f x s _45950)). Qed.
Lemma lem3995164 {A B : Type'} (_45950 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term441 A B f x s _45950.
Proof. exact (EQ_MP (@lem3995163 A B f x s _45950) (@lem3995162 A B _45950 f x s h1)). Qed.
Lemma lem3995165 {A B : Type'} (_45950 : A) (_45951 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term458 A B f x s _45950 _45951.
Proof. exact (@lem3995164 A B _45950 f x s h1 _45951). Qed.
Lemma lem3995166 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45950 : A) (_45951 : A) : (term458 A B f x s _45950 _45951) = (term439 A B f x s _45950 _45951).
Proof. exact (eq_refl (term458 A B f x s _45950 _45951)). Qed.
Lemma lem3995207 {A : Type'} (_45965 : A) (h1 : term213 A) : term459 A _45965.
Proof. exact (@lem3994901 A h1 _45965). Qed.
Lemma lem3995208 {A : Type'} (_45965 : A) : (term459 A _45965) = (term454 A _45965).
Proof. exact (eq_refl (term459 A _45965)). Qed.
Lemma lem3995209 {A : Type'} (_45965 : A) (h1 : term213 A) : term454 A _45965.
Proof. exact (EQ_MP (@lem3995208 A _45965) (@lem3995207 A _45965 h1)). Qed.
Lemma lem3995210 {A : Type'} (_45965 : A) (_45966 : A) (h1 : term213 A) : term460 A _45965 _45966.
Proof. exact (@lem3995209 A _45965 h1 _45966). Qed.
Lemma lem3995211 {A : Type'} (_45966 : A) (_45965 : A) : (term460 A _45965 _45966) = (term452 A _45966 _45965).
Proof. exact (eq_refl (term460 A _45965 _45966)). Qed.
Lemma lem3995212 {A : Type'} (_45966 : A) (_45965 : A) (h1 : term213 A) : term452 A _45966 _45965.
Proof. exact (EQ_MP (@lem3995211 A _45966 _45965) (@lem3995210 A _45965 _45966 h1)). Qed.
Lemma lem3995213 {A : Type'} (_45966 : A) (_45965 : A) (_45967 : A -> Prop) (h1 : term213 A) : term461 A _45966 _45965 _45967.
Proof. exact (@lem3995212 A _45966 _45965 h1 _45967). Qed.
Lemma lem3995214 {A : Type'} (_45966 : A) (_45965 : A) (_45967 : A -> Prop) : (term461 A _45966 _45965 _45967) = (term449 A _45966 _45965 _45967).
Proof. exact (eq_refl (term461 A _45966 _45965 _45967)). Qed.
Lemma lem3995215 {A : Type'} (_45966 : A) (_45965 : A) (_45967 : A -> Prop) (h1 : term213 A) : term449 A _45966 _45965 _45967.
Proof. exact (EQ_MP (@lem3995214 A _45966 _45965 _45967) (@lem3995213 A _45966 _45965 _45967 h1)). Qed.
Lemma lem3995317 {A B : Type'} (_45950 : A) (_45951 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term439 A B f x s _45950 _45951.
Proof. exact (EQ_MP (@lem3995166 A B f x s _45950 _45951) (@lem3995165 A B _45950 _45951 f x s h1)). Qed.
Lemma lem3995363 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term450 A x' y.
Proof. exact (proj2 (@lem3994708 A B f s x' y h1)). Qed.
Lemma lem3995375 {A : Type'} (_45966 : A) (_45965 : A) (_45967 : A -> Prop) (h1 : term213 A) : term462 A _45966 _45965 _45967.
Proof. exact (proj2 (@lem3995215 A _45966 _45965 _45967 h1)). Qed.
Lemma lem3995425 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) : term584 A B f s.
Proof. exact (h1). Qed.
Lemma lem3995457 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : (term32 A B f s) = (@CARD A s).
Proof. exact (h1). Qed.
Lemma lem3995677 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : (@I (A -> B) f x') = (@I (A -> B) f y).
Proof. exact (proj1 (@lem3994704 A B f s x' y h1)). Qed.
Lemma lem3995678 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term464 A B x' f y.
Proof. exact (fun h0 : term437 A B x' f y => @lem3995677 A B f s x' y h1). Qed.
Lemma lem3995680 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995681 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term464 A B x' f y) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (@lem3995680 ((@I (A -> B) f x') = (@I (A -> B) f y))). Qed.
Lemma lem3995682 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : (@I (A -> B) f x') = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem3995681 A B x' f y) (@lem3995678 A B f s x' y h1)). Qed.
Lemma lem3995684 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : @IN A y s.
Proof. exact (proj1 (@lem3994706 A B f s x' y h1)). Qed.
Lemma lem3995685 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term466 A y s.
Proof. exact (fun h0 : term124 A y s => @lem3995684 A B f s x' y h1). Qed.
Lemma lem3995687 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995688 {A : Type'} (y : A) (s : A -> Prop) : (term466 A y s) = (@IN A y s).
Proof. exact (@lem3995687 (@IN A y s)). Qed.
Lemma lem3995689 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : @IN A y s.
Proof. exact (EQ_MP (@lem3995688 A y s) (@lem3995685 A B f s x' y h1)). Qed.
Lemma lem3995691 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3995692 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) : (term462 A _45966 _45965 _45967) = (term468 A _45965 _45966 _45967).
Proof. exact (@lem3995691 (term124 A _45965 _45967) (term259 A _45965 _45966 _45967)). Qed.
Lemma lem3995694 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3995695 {A : Type'} (_45965 : A) (_45967 : A -> Prop) : (term470 A _45965 _45967) = (@IN A _45965 _45967).
Proof. exact (@lem3995694 (@IN A _45965 _45967)). Qed.
Lemma lem3995696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3995697 {A : Type'} (_45965 : A) (_45967 : A -> Prop) : (term471 A _45965 _45967) = (term472 A _45965 _45967).
Proof. exact (MK_COMB (@lem3995696) (@lem3995695 A _45965 _45967)). Qed.
Lemma lem3995698 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) : (term259 A _45965 _45966 _45967) = (term259 A _45965 _45966 _45967).
Proof. exact (eq_refl (term259 A _45965 _45966 _45967)). Qed.
Lemma lem3995699 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) : (term468 A _45965 _45966 _45967) = (term473 A _45965 _45966 _45967).
Proof. exact (MK_COMB (@lem3995697 A _45965 _45967) (@lem3995698 A _45965 _45966 _45967)). Qed.
Lemma lem3995700 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) : (term462 A _45966 _45965 _45967) = (term473 A _45965 _45966 _45967).
Proof. exact (TRANS (@lem3995692 A _45965 _45966 _45967) (@lem3995699 A _45965 _45966 _45967)). Qed.
Lemma lem3995703 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) (h1 : term213 A) : term473 A _45965 _45966 _45967.
Proof. exact (EQ_MP (@lem3995700 A _45965 _45966 _45967) (@lem3995375 A _45966 _45965 _45967 h1)). Qed.
Lemma lem3995704 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) (h1 : term213 A) : term473 A _45965 _45966 _45967.
Proof. exact (@lem3995703 A _45965 _45966 _45967 h1). Qed.
Lemma lem3995705 {A : Type'} (y : A) (_45966 : A) (s : A -> Prop) (h1 : term213 A) : term473 A y _45966 s.
Proof. exact (@lem3995704 A y _45966 s h1). Qed.
Lemma lem3995708 {A B : Type'} (_45966 : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A y _45966 s.
Proof. exact (@lem3995705 A y _45966 s h1 (@lem3995689 A B f s x' y h2)). Qed.
Lemma lem3995709 {A B : Type'} (_45966 : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A y _45966 s.
Proof. exact (@lem3995708 A B _45966 f s x' y h1 h2). Qed.
Lemma lem3995710 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A y x s.
Proof. exact (@lem3995709 A B x f s x' y h1 h2). Qed.
Lemma lem3995711 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term474 A y x s.
Proof. exact (fun h0 : term475 A y x s => @lem3995710 A B x f s x' y h1 h2). Qed.
Lemma lem3995713 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995714 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term474 A y x s) = (term259 A y x s).
Proof. exact (@lem3995713 (term259 A y x s)). Qed.
Lemma lem3995715 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A y x s.
Proof. exact (EQ_MP (@lem3995714 A y x s) (@lem3995711 A B x f s x' y h1 h2)). Qed.
Lemma lem3995717 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : @IN A x' s.
Proof. exact (proj1 (@lem3994708 A B f s x' y h1)). Qed.
Lemma lem3995718 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term466 A x' s.
Proof. exact (fun h0 : term124 A x' s => @lem3995717 A B f s x' y h1). Qed.
Lemma lem3995720 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995721 {A : Type'} (x' : A) (s : A -> Prop) : (term466 A x' s) = (@IN A x' s).
Proof. exact (@lem3995720 (@IN A x' s)). Qed.
Lemma lem3995722 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : @IN A x' s.
Proof. exact (EQ_MP (@lem3995721 A x' s) (@lem3995718 A B f s x' y h1)). Qed.
Lemma lem3995724 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) (h1 : term213 A) : term473 A _45965 _45966 _45967.
Proof. exact (EQ_MP (@lem3995700 A _45965 _45966 _45967) (@lem3995375 A _45966 _45965 _45967 h1)). Qed.
Lemma lem3995725 {A : Type'} (_45965 : A) (_45966 : A) (_45967 : A -> Prop) (h1 : term213 A) : term473 A _45965 _45966 _45967.
Proof. exact (@lem3995724 A _45965 _45966 _45967 h1). Qed.
Lemma lem3995726 {A : Type'} (x' : A) (_45966 : A) (s : A -> Prop) (h1 : term213 A) : term473 A x' _45966 s.
Proof. exact (@lem3995725 A x' _45966 s h1). Qed.
Lemma lem3995729 {A B : Type'} (_45966 : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A x' _45966 s.
Proof. exact (@lem3995726 A x' _45966 s h1 (@lem3995722 A B f s x' y h2)). Qed.
Lemma lem3995730 {A B : Type'} (_45966 : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A x' _45966 s.
Proof. exact (@lem3995729 A B _45966 f s x' y h1 h2). Qed.
Lemma lem3995731 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A x' x s.
Proof. exact (@lem3995730 A B x f s x' y h1 h2). Qed.
Lemma lem3995732 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term474 A x' x s.
Proof. exact (fun h0 : term475 A x' x s => @lem3995731 A B x f s x' y h1 h2). Qed.
Lemma lem3995734 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995735 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term474 A x' x s) = (term259 A x' x s).
Proof. exact (@lem3995734 (term259 A x' x s)). Qed.
Lemma lem3995736 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term259 A x' x s.
Proof. exact (EQ_MP (@lem3995735 A x' x s) (@lem3995732 A B x f s x' y h1 h2)). Qed.
Lemma lem3995754 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3995755 {A : Type'} (x : A) (s : A -> Prop) (_45950 : A) (_45951 : A) : (term341 A x s _45950 _45951) = (term477 A x s _45950 _45951).
Proof. exact (@lem3995754 (term475 A _45950 x s) (term475 A _45951 x s) (_45950 = _45951)). Qed.
Lemma lem3995769 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3995770 {A : Type'} (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term478 A x s _45950 _45951) = (term479 A _45950 _45951 x s).
Proof. exact (@lem3995769 (_45950 = _45951) (term475 A _45951 x s)). Qed.
Lemma lem3995778 {A : Type'} (_45950 : A) (x : A) (s : A -> Prop) : (term339 A _45950 x s) = (term339 A _45950 x s).
Proof. exact (eq_refl (term339 A _45950 x s)). Qed.
Lemma lem3995779 {A : Type'} (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term477 A x s _45950 _45951) = (term480 A _45950 _45951 x s).
Proof. exact (MK_COMB (@lem3995778 A _45950 x s) (@lem3995770 A _45950 _45951 x s)). Qed.
Lemma lem3995783 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3995784 {A : Type'} (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term480 A _45950 _45951 x s) = (term481 A _45950 _45951 x s).
Proof. exact (@lem3995783 (_45950 = _45951) (term475 A _45950 x s) (term475 A _45951 x s)). Qed.
Lemma lem3995802 {A : Type'} (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term477 A x s _45950 _45951) = (term481 A _45950 _45951 x s).
Proof. exact (TRANS (@lem3995779 A _45950 _45951 x s) (@lem3995784 A _45950 _45951 x s)). Qed.
Lemma lem3995803 {A : Type'} (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term341 A x s _45950 _45951) = (term481 A _45950 _45951 x s).
Proof. exact (TRANS (@lem3995755 A x s _45950 _45951) (@lem3995802 A _45950 _45951 x s)). Qed.
Lemma lem3995804 {A B : Type'} (_45950 : A) (f : A -> B) (_45951 : A) : (term438 A B _45950 f _45951) = (term438 A B _45950 f _45951).
Proof. exact (eq_refl (term438 A B _45950 f _45951)). Qed.
Lemma lem3995805 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45950 _45951) = (term482 A B f _45950 _45951 x s).
Proof. exact (MK_COMB (@lem3995804 A B _45950 f _45951) (@lem3995803 A _45950 _45951 x s)). Qed.
Lemma lem3995809 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3995810 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term482 A B f _45950 _45951 x s) = (term483 A B f _45950 _45951 x s).
Proof. exact (@lem3995809 (_45950 = _45951) (term437 A B _45950 f _45951) (term484 A _45950 _45951 x s)). Qed.
Lemma lem3995840 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45950 _45951) = (term483 A B f _45950 _45951 x s).
Proof. exact (TRANS (@lem3995805 A B f _45950 _45951 x s) (@lem3995810 A B f _45950 _45951 x s)). Qed.
Lemma lem3995841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3995842 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term485 A B f x s _45950 _45951) = (term486 A B f _45950 _45951 x s).
Proof. exact (MK_COMB (@lem3995841) (@lem3995840 A B f _45950 _45951 x s)). Qed.
Lemma lem3995870 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3995871 {A : Type'} (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term484 A _45951 _45950 x s) = (term484 A _45950 _45951 x s).
Proof. exact (@lem3995870 (term475 A _45950 x s) (term475 A _45951 x s)). Qed.
Lemma lem3995877 {A B : Type'} (_45950 : A) (f : A -> B) (_45951 : A) : (term438 A B _45950 f _45951) = (term438 A B _45950 f _45951).
Proof. exact (eq_refl (term438 A B _45950 f _45951)). Qed.
Lemma lem3995878 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term487 A B f _45951 _45950 x s) = (term488 A B f _45950 _45951 x s).
Proof. exact (MK_COMB (@lem3995877 A B _45950 f _45951) (@lem3995871 A _45950 _45951 x s)). Qed.
Lemma lem3995889 {A : Type'} (_45950 : A) (_45951 : A) : (term489 A _45950 _45951) = (term489 A _45950 _45951).
Proof. exact (eq_refl (term489 A _45950 _45951)). Qed.
Lemma lem3995890 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : (term490 A B f _45951 _45950 x s) = (term483 A B f _45950 _45951 x s).
Proof. exact (MK_COMB (@lem3995889 A _45950 _45951) (@lem3995878 A B f _45950 _45951 x s)). Qed.
Lemma lem3995901 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : ((term439 A B f x s _45950 _45951) = (term490 A B f _45951 _45950 x s)) = ((term483 A B f _45950 _45951 x s) = (term483 A B f _45950 _45951 x s)).
Proof. exact (MK_COMB (@lem3995842 A B f _45950 _45951 x s) (@lem3995890 A B f _45950 _45951 x s)). Qed.
Lemma lem3995903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3995904 (x : Prop) : (x = x) = True.
Proof. exact (@lem3995903 Prop x). Qed.
Lemma lem3995905 {A B : Type'} (f : A -> B) (_45950 : A) (_45951 : A) (x : A) (s : A -> Prop) : ((term483 A B f _45950 _45951 x s) = (term483 A B f _45950 _45951 x s)) = True.
Proof. exact (@lem3995904 (term483 A B f _45950 _45951 x s)). Qed.
Lemma lem3995906 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : ((term439 A B f x s _45950 _45951) = (term490 A B f _45951 _45950 x s)) = True.
Proof. exact (TRANS (@lem3995901 A B f _45950 _45951 x s) (@lem3995905 A B f _45950 _45951 x s)). Qed.
Lemma lem3995907 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : True = ((term439 A B f x s _45950 _45951) = (term490 A B f _45951 _45950 x s)).
Proof. exact (SYM (@lem3995906 A B f _45951 _45950 x s)). Qed.
Lemma lem3995908 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term439 A B f x s _45950 _45951) = (term490 A B f _45951 _45950 x s).
Proof. exact (EQ_MP (@lem3995907 A B f _45951 _45950 x s) (@lem0)). Qed.
Lemma lem3995909 {A B : Type'} (_45951 : A) (_45950 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term490 A B f _45951 _45950 x s.
Proof. exact (EQ_MP (@lem3995908 A B f _45951 _45950 x s) (@lem3995317 A B _45950 _45951 f x s h1)). Qed.
Lemma lem3995911 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3995912 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45950 : A) (_45951 : A) : (term490 A B f _45951 _45950 x s) = (term491 A B f x s _45950 _45951).
Proof. exact (@lem3995911 (term487 A B f _45951 _45950 x s) (_45950 = _45951)). Qed.
Lemma lem3995914 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3995915 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term494 A B f _45951 _45950 x s) = (term495 A B f _45951 _45950 x s).
Proof. exact (@lem3995914 (term437 A B _45950 f _45951) (term484 A _45951 _45950 x s)). Qed.
Lemma lem3995917 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3995918 {A B : Type'} (_45950 : A) (f : A -> B) (_45951 : A) : (term496 A B _45950 f _45951) = ((@I (A -> B) f _45950) = (@I (A -> B) f _45951)).
Proof. exact (@lem3995917 ((@I (A -> B) f _45950) = (@I (A -> B) f _45951))). Qed.
Lemma lem3995919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3995920 {A B : Type'} (_45950 : A) (f : A -> B) (_45951 : A) : (term497 A B _45950 f _45951) = (term444 A B _45950 f _45951).
Proof. exact (MK_COMB (@lem3995919) (@lem3995918 A B _45950 f _45951)). Qed.
Lemma lem3995922 (a : Prop) (b : Prop) : (term492 a b) = (term493 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3995923 {A : Type'} (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term498 A _45951 _45950 x s) = (term499 A _45951 _45950 x s).
Proof. exact (@lem3995922 (term475 A _45951 x s) (term475 A _45950 x s)). Qed.
Lemma lem3995925 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3995926 {A : Type'} (_45951 : A) (x : A) (s : A -> Prop) : (term500 A _45951 x s) = (term259 A _45951 x s).
Proof. exact (@lem3995925 (term259 A _45951 x s)). Qed.
Lemma lem3995927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3995928 {A : Type'} (_45951 : A) (x : A) (s : A -> Prop) : (term501 A _45951 x s) = (term502 A _45951 x s).
Proof. exact (MK_COMB (@lem3995927) (@lem3995926 A _45951 x s)). Qed.
Lemma lem3995930 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3995931 {A : Type'} (_45950 : A) (x : A) (s : A -> Prop) : (term500 A _45950 x s) = (term259 A _45950 x s).
Proof. exact (@lem3995930 (term259 A _45950 x s)). Qed.
Lemma lem3995932 {A : Type'} (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term499 A _45951 _45950 x s) = (term503 A _45951 _45950 x s).
Proof. exact (MK_COMB (@lem3995928 A _45951 x s) (@lem3995931 A _45950 x s)). Qed.
Lemma lem3995933 {A : Type'} (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term498 A _45951 _45950 x s) = (term503 A _45951 _45950 x s).
Proof. exact (TRANS (@lem3995923 A _45951 _45950 x s) (@lem3995932 A _45951 _45950 x s)). Qed.
Lemma lem3995934 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term495 A B f _45951 _45950 x s) = (term504 A B f _45951 _45950 x s).
Proof. exact (MK_COMB (@lem3995920 A B _45950 f _45951) (@lem3995933 A _45951 _45950 x s)). Qed.
Lemma lem3995935 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term494 A B f _45951 _45950 x s) = (term504 A B f _45951 _45950 x s).
Proof. exact (TRANS (@lem3995915 A B f _45951 _45950 x s) (@lem3995934 A B f _45951 _45950 x s)). Qed.
Lemma lem3995936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3995937 {A B : Type'} (f : A -> B) (_45951 : A) (_45950 : A) (x : A) (s : A -> Prop) : (term505 A B f _45951 _45950 x s) = (term506 A B f _45951 _45950 x s).
Proof. exact (MK_COMB (@lem3995936) (@lem3995935 A B f _45951 _45950 x s)). Qed.
Lemma lem3995938 {A : Type'} (_45950 : A) (_45951 : A) : (_45950 = _45951) = (_45950 = _45951).
Proof. exact (eq_refl (_45950 = _45951)). Qed.
Lemma lem3995939 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45950 : A) (_45951 : A) : (term491 A B f x s _45950 _45951) = (term507 A B f x s _45950 _45951).
Proof. exact (MK_COMB (@lem3995937 A B f _45951 _45950 x s) (@lem3995938 A _45950 _45951)). Qed.
Lemma lem3995940 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (_45950 : A) (_45951 : A) : (term490 A B f _45951 _45950 x s) = (term507 A B f x s _45950 _45951).
Proof. exact (TRANS (@lem3995912 A B f x s _45950 _45951) (@lem3995939 A B f x s _45950 _45951)). Qed.
Lemma lem3995942 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term503 A y x' x s.
Proof. exact (conj (@lem3995715 A B x f s x' y h1 h2) (@lem3995736 A B x f s x' y h1 h2)). Qed.
Lemma lem3995943 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term446 A B f s x' y) : term504 A B f y x' x s.
Proof. exact (conj (@lem3995682 A B f s x' y h2) (@lem3995942 A B x f s x' y h1 h2)). Qed.
Lemma lem3995945 {A B : Type'} (_45950 : A) (_45951 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s _45950 _45951.
Proof. exact (EQ_MP (@lem3995940 A B f x s _45950 _45951) (@lem3995909 A B _45951 _45950 f x s h1)). Qed.
Lemma lem3995946 {A B : Type'} (_45950 : A) (_45951 : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s _45950 _45951.
Proof. exact (@lem3995945 A B _45950 _45951 f x s h1). Qed.
Lemma lem3995947 {A B : Type'} (x' : A) (y : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term125 A B f x s) : term507 A B f x s x' y.
Proof. exact (@lem3995946 A B x' y f x s h1). Qed.
Lemma lem3995950 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x' y) : x' = y.
Proof. exact (@lem3995947 A B x' y f x s h2 (@lem3995943 A B x f s x' y h1 h3)). Qed.
Lemma lem3995951 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x' y) : term508 A x' y.
Proof. exact (fun h0 : term450 A x' y => @lem3995950 A B x f s x' y h1 h2 h3). Qed.
Lemma lem3995953 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995954 {A : Type'} (x' : A) (y : A) : (term508 A x' y) = (x' = y).
Proof. exact (@lem3995953 (x' = y)). Qed.
Lemma lem3995955 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x' y) : x' = y.
Proof. exact (EQ_MP (@lem3995954 A x' y) (@lem3995951 A B x f s x' y h1 h2 h3)). Qed.
Lemma lem3995958 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3995960 {A : Type'} (x' : A) (y : A) : (term450 A x' y) = (term509 A x' y).
Proof. exact (@lem3995958 (x' = y)). Qed.
Lemma lem3995963 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term446 A B f s x' y) : term509 A x' y.
Proof. exact (EQ_MP (@lem3995960 A x' y) (@lem3995363 A B f s x' y h1)). Qed.
Lemma lem3995966 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x' y) : False.
Proof. exact (@lem3995963 A B f s x' y h3 (@lem3995955 A B x f s x' y h1 h2 h3)). Qed.
Lemma lem3995967 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x' y) : term510.
Proof. exact (fun h0 : ~ False => @lem3995966 A B x f s x' y h1 h2 h3). Qed.
Lemma lem3995969 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3995970 : term510 = False.
Proof. exact (@lem3995969 False). Qed.
Lemma lem3995971 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) (y : A) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term446 A B f s x' y) : False.
Proof. exact (EQ_MP (@lem3995970) (@lem3995967 A B x f s x' y h1 h2 h3)). Qed.
Lemma lem3996102 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem3996103 (_46062 : nat) (_46063 : nat) (h1 : _46062 = _46063) : _46062 = _46063.
Proof. exact (h1). Qed.
Lemma lem3996104 (_46062 : nat) (_46063 : nat) (h1 : _46062 = _46063) : (S _46062) = (S _46063).
Proof. exact (MK_COMB (@lem3996102) (@lem3996103 _46062 _46063 h1)). Qed.
Lemma lem3996105 (_46062 : nat) (_46063 : nat) : term613 _46062 _46063.
Proof. exact (fun h0 : _46062 = _46063 => @lem3996104 _46062 _46063 h0). Qed.
Lemma lem3996107 (a : Prop) (b : Prop) : (a -> b) = (term515 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3996108 (_46062 : nat) (_46063 : nat) : (term613 _46062 _46063) = (term614 _46062 _46063).
Proof. exact (@lem3996107 (_46062 = _46063) ((S _46062) = (S _46063))). Qed.
Lemma lem3996109 (_46062 : nat) (_46063 : nat) : term614 _46062 _46063.
Proof. exact (EQ_MP (@lem3996108 _46062 _46063) (@lem3996105 _46062 _46063)). Qed.
Lemma lem3996155 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : (term32 A B f s) = (@CARD A s).
Proof. exact (h1). Qed.
Lemma lem3996156 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : term615 A B f s.
Proof. exact (fun h0 : term616 A B f s => @lem3996155 A B f s h1). Qed.
Lemma lem3996158 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3996159 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term615 A B f s) = ((term32 A B f s) = (@CARD A s)).
Proof. exact (@lem3996158 ((term32 A B f s) = (@CARD A s))). Qed.
Lemma lem3996160 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : (term32 A B f s) = (@CARD A s).
Proof. exact (EQ_MP (@lem3996159 A B f s) (@lem3996156 A B f s h1)). Qed.
Lemma lem3996166 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3996167 (_46062 : nat) (_46063 : nat) : (term614 _46062 _46063) = (term617 _46062 _46063).
Proof. exact (@lem3996166 ((S _46062) = (S _46063)) (term618 _46062 _46063)). Qed.
Lemma lem3996177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3996178 (_46062 : nat) (_46063 : nat) : (term619 _46062 _46063) = (term620 _46062 _46063).
Proof. exact (MK_COMB (@lem3996177) (@lem3996167 _46062 _46063)). Qed.
Lemma lem3996188 (_46062 : nat) (_46063 : nat) : (term617 _46062 _46063) = (term617 _46062 _46063).
Proof. exact (eq_refl (term617 _46062 _46063)). Qed.
Lemma lem3996189 (_46062 : nat) (_46063 : nat) : ((term614 _46062 _46063) = (term617 _46062 _46063)) = ((term617 _46062 _46063) = (term617 _46062 _46063)).
Proof. exact (MK_COMB (@lem3996178 _46062 _46063) (@lem3996188 _46062 _46063)). Qed.
Lemma lem3996191 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3996192 (x : Prop) : (x = x) = True.
Proof. exact (@lem3996191 Prop x). Qed.
Lemma lem3996193 (_46062 : nat) (_46063 : nat) : ((term617 _46062 _46063) = (term617 _46062 _46063)) = True.
Proof. exact (@lem3996192 (term617 _46062 _46063)). Qed.
Lemma lem3996194 (_46062 : nat) (_46063 : nat) : ((term614 _46062 _46063) = (term617 _46062 _46063)) = True.
Proof. exact (TRANS (@lem3996189 _46062 _46063) (@lem3996193 _46062 _46063)). Qed.
Lemma lem3996195 (_46062 : nat) (_46063 : nat) : True = ((term614 _46062 _46063) = (term617 _46062 _46063)).
Proof. exact (SYM (@lem3996194 _46062 _46063)). Qed.
Lemma lem3996196 (_46062 : nat) (_46063 : nat) : (term614 _46062 _46063) = (term617 _46062 _46063).
Proof. exact (EQ_MP (@lem3996195 _46062 _46063) (@lem0)). Qed.
Lemma lem3996197 (_46062 : nat) (_46063 : nat) : term617 _46062 _46063.
Proof. exact (EQ_MP (@lem3996196 _46062 _46063) (@lem3996109 _46062 _46063)). Qed.
Lemma lem3996199 (b : Prop) (a : Prop) : (a \/ b) = (term467 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3996200 (_46062 : nat) (_46063 : nat) : (term617 _46062 _46063) = (term621 _46062 _46063).
Proof. exact (@lem3996199 (term618 _46062 _46063) ((S _46062) = (S _46063))). Qed.
Lemma lem3996202 (a : Prop) : (term469 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3996203 (_46062 : nat) (_46063 : nat) : (term622 _46062 _46063) = (_46062 = _46063).
Proof. exact (@lem3996202 (_46062 = _46063)). Qed.
Lemma lem3996204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3996205 (_46062 : nat) (_46063 : nat) : (term623 _46062 _46063) = (term624 _46062 _46063).
Proof. exact (MK_COMB (@lem3996204) (@lem3996203 _46062 _46063)). Qed.
Lemma lem3996206 (_46062 : nat) (_46063 : nat) : ((S _46062) = (S _46063)) = ((S _46062) = (S _46063)).
Proof. exact (eq_refl ((S _46062) = (S _46063))). Qed.
Lemma lem3996207 (_46062 : nat) (_46063 : nat) : (term621 _46062 _46063) = (term613 _46062 _46063).
Proof. exact (MK_COMB (@lem3996205 _46062 _46063) (@lem3996206 _46062 _46063)). Qed.
Lemma lem3996208 (_46062 : nat) (_46063 : nat) : (term617 _46062 _46063) = (term613 _46062 _46063).
Proof. exact (TRANS (@lem3996200 _46062 _46063) (@lem3996207 _46062 _46063)). Qed.
Lemma lem3996211 (_46062 : nat) (_46063 : nat) : term613 _46062 _46063.
Proof. exact (EQ_MP (@lem3996208 _46062 _46063) (@lem3996197 _46062 _46063)). Qed.
Lemma lem3996212 {A B : Type'} (f : A -> B) (s : A -> Prop) : term625 A B f s.
Proof. exact (@lem3996211 (term32 A B f s) (@CARD A s)). Qed.
Lemma lem3996215 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : (term156 A B f s) = (term175 A s).
Proof. exact (@lem3996212 A B f s (@lem3996160 A B f s h1)). Qed.
Lemma lem3996216 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : term626 A B f s.
Proof. exact (fun h0 : term584 A B f s => @lem3996215 A B f s h1). Qed.
Lemma lem3996218 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3996219 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term626 A B f s) = ((term156 A B f s) = (term175 A s)).
Proof. exact (@lem3996218 ((term156 A B f s) = (term175 A s))). Qed.
Lemma lem3996220 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : (term32 A B f s) = (@CARD A s)) : (term156 A B f s) = (term175 A s).
Proof. exact (EQ_MP (@lem3996219 A B f s) (@lem3996216 A B f s h1)). Qed.
Lemma lem3996223 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3996225 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term584 A B f s) = (term627 A B f s).
Proof. exact (@lem3996223 ((term156 A B f s) = (term175 A s))). Qed.
Lemma lem3996228 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) : term627 A B f s.
Proof. exact (EQ_MP (@lem3996225 A B f s) (@lem3995425 A B f s h1)). Qed.
Lemma lem3996231 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (@lem3996228 A B f s h1 (@lem3996220 A B f s h2)). Qed.
Lemma lem3996232 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : term510.
Proof. exact (fun h0 : ~ False => @lem3996231 A B f s h1 h2). Qed.
Lemma lem3996234 (p : Prop) : (term465 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3996235 : term510 = False.
Proof. exact (@lem3996234 False). Qed.
Lemma lem3996236 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996235) (@lem3996232 A B f s h1 h2)). Qed.
Lemma lem3996237 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : ((term32 A B f s) = (@CARD A s)) = False.
Proof. exact (prop_ext (fun h3 : (term32 A B f s) = (@CARD A s) => @lem3996236 A B f s h1 h2) (fun h3 : False => @lem3995457 A B f s h2)). Qed.
Lemma lem3996238 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996237 A B f s h1 h2) (@lem3995457 A B f s h2)). Qed.
Lemma lem3996239 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : (term584 A B f s) = False.
Proof. exact (prop_ext (fun h3 : term584 A B f s => @lem3996238 A B f s h1 h2) (fun h3 : False => @lem3995425 A B f s h1)). Qed.
Lemma lem3996240 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996239 A B f s h1 h2) (@lem3995425 A B f s h1)). Qed.
Lemma lem3996241 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : ((term32 A B f s) = (@CARD A s)) = False.
Proof. exact (prop_ext (fun h3 : (term32 A B f s) = (@CARD A s) => @lem3996240 A B f s h1 h2) (fun h3 : False => @lem3995161 A B f s h2)). Qed.
Lemma lem3996242 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996241 A B f s h1 h2) (@lem3995161 A B f s h2)). Qed.
Lemma lem3996243 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : (term584 A B f s) = False.
Proof. exact (prop_ext (fun h3 : term584 A B f s => @lem3996242 A B f s h1 h2) (fun h3 : False => @lem3994995 A B f s h1)). Qed.
Lemma lem3996244 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996243 A B f s h1 h2) (@lem3994995 A B f s h1)). Qed.
Lemma lem3996245 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : ((term32 A B f s) = (@CARD A s)) = False.
Proof. exact (prop_ext (fun h3 : (term32 A B f s) = (@CARD A s) => @lem3996244 A B f s h1 h2) (fun h3 : False => @lem3995161 A B f s h2)). Qed.
Lemma lem3996246 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996245 A B f s h1 h2) (@lem3995161 A B f s h2)). Qed.
Lemma lem3996247 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : (term584 A B f s) = False.
Proof. exact (prop_ext (fun h3 : term584 A B f s => @lem3996246 A B f s h1 h2) (fun h3 : False => @lem3994995 A B f s h1)). Qed.
Lemma lem3996248 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term584 A B f s) (h2 : (term32 A B f s) = (@CARD A s)) : False.
Proof. exact (EQ_MP (@lem3996247 A B f s h1 h2) (@lem3994995 A B f s h1)). Qed.
Lemma lem3996249 {A B : Type'} (x : A) (x' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term331 A B x' y f s) : False.
Proof. exact (or_elim (@lem3994697 A B x' y f s h4) (fun h0 : term446 A B f s x' y => @lem3995971 A B x f s x' y h1 h2 h0) (fun h0 : (term32 A B f s) = (@CARD A s) => @lem3996248 A B f s h3 h0)). Qed.
Lemma lem3996250 {A B : Type'} (x : A) (x' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term331 A B x' y f s) : (term584 A B f s) = False.
Proof. exact (prop_ext (fun h5 : term584 A B f s => @lem3996249 A B x x' y f s h1 h2 h3 h4) (fun h5 : False => @lem3994401 A B f s h3)). Qed.
Lemma lem3996251 {A B : Type'} (x : A) (x' : A) (y : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term331 A B x' y f s) : False.
Proof. exact (EQ_MP (@lem3996250 A B x x' y f s h1 h2 h3 h4) (@lem3994401 A B f s h3)). Qed.
Lemma lem3996252 {A B : Type'} (x : A) (x' : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term334 A B x' f s) (h4 : term584 A B f s) : False.
Proof. exact (ex_elim (@lem3994270 A B x' f s h3) (fun y : A => fun h0 : term333 A B x' f s y => @lem3996251 A B x x' y f s h1 h2 h4 h0)). Qed.
Lemma lem3996253 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term48 A B f s) : False.
Proof. exact (ex_elim (@lem3992758 A B f s h4) (fun x' : A => fun h0 : term335 A B f s x' => @lem3996252 A B x x' f s h1 h2 h0 h3)). Qed.
Lemma lem3996254 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term48 A B f s) : (term584 A B f s) = False.
Proof. exact (prop_ext (fun h5 : term584 A B f s => @lem3996253 A B x f s h1 h2 h3 h4) (fun h5 : False => @lem3992928 A B f s h3)). Qed.
Lemma lem3996255 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term48 A B f s) : False.
Proof. exact (EQ_MP (@lem3996254 A B x f s h1 h2 h3 h4) (@lem3992928 A B f s h3)). Qed.
Lemma lem3996256 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term48 A B f s) : term219.
Proof. exact (fun h0 : term214 => @lem3996255 A B x f s h1 h2 h3 h4). Qed.
Lemma lem3996257 : term219 = term220.
Proof. exact (@lem69 term214). Qed.
Lemma lem3996258 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term48 A B f s) : term220.
Proof. exact (EQ_MP (@lem3996257) (@lem3996256 A B x f s h1 h2 h3 h4)). Qed.
Lemma lem3996259 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term213 A) (h2 : term125 A B f x s) (h3 : term584 A B f s) (h4 : term48 A B f s) : term223 B.
Proof. exact (fun h0 : term213 B => @lem3996258 A B x f s h1 h2 h3 h4). Qed.
Lemma lem3996260 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term584 A B f s) (h3 : term48 A B f s) : term225 A B.
Proof. exact (fun h0 : term213 A => @lem3996259 A B x f s h0 h1 h2 h3). Qed.
Lemma lem3996261 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term48 A B f s) : term591 A B f s.
Proof. exact (fun h0 : term584 A B f s => @lem3996260 A B x f s h1 h0 h2). Qed.
Lemma lem3996262 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term48 A B f s) : term593 A B x f s.
Proof. exact (fun h0 : term170 A B x f s => @lem3996261 A B x f s h1 h2). Qed.
Lemma lem3996263 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term595 A B x f s.
Proof. exact (fun h0 : term125 A B f x s => @lem3996262 A B x f s h0 h1). Qed.
Lemma lem3996264 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term597 A B x f s.
Proof. exact (fun h0 : @FINITE A s => @lem3996263 A B x f s h1). Qed.
Lemma lem3996265 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term599 A B x f s.
Proof. exact (fun h0 : term124 A x s => @lem3996264 A B x f s h1). Qed.
Lemma lem3996266 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term600 A B x f s.
Proof. exact (fun h0 : term48 A B f s => @lem3996265 A B x f s h0). Qed.
Lemma lem3996271 {A B : Type'} (f : A -> B) (s : A -> Prop) : term604 A B f s.
Proof. exact (fun x : A => @lem3996266 A B x f s). Qed.
Lemma lem3996276 {A B : Type'} (s : A -> Prop) : term608 A B s.
Proof. exact (fun f : A -> B => @lem3996271 A B f s). Qed.
Lemma lem3996281 {A B : Type'} : term612 A B.
Proof. exact (fun s : A -> Prop => @lem3996276 A B s). Qed.
Lemma lem3996282 {A B : Type'} : term611 A B.
Proof. exact (EQ_MP (@lem3992596 A B) (@lem3996281 A B)). Qed.
Lemma lem3996283 {A B : Type'} (s : A -> Prop) : term628 A B s.
Proof. exact (@lem3996282 A B s). Qed.
Lemma lem3996284 {A B : Type'} (s : A -> Prop) : (term628 A B s) = (term607 A B s).
Proof. exact (eq_refl (term628 A B s)). Qed.
Lemma lem3996285 {A B : Type'} (s : A -> Prop) : term607 A B s.
Proof. exact (EQ_MP (@lem3996284 A B s) (@lem3996283 A B s)). Qed.
Lemma lem3996286 {A B : Type'} (s : A -> Prop) (f : A -> B) : term629 A B s f.
Proof. exact (@lem3996285 A B s f). Qed.
Lemma lem3996287 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term629 A B s f) = (term603 A B f s).
Proof. exact (eq_refl (term629 A B s f)). Qed.
Lemma lem3996288 {A B : Type'} (f : A -> B) (s : A -> Prop) : term603 A B f s.
Proof. exact (EQ_MP (@lem3996287 A B f s) (@lem3996286 A B s f)). Qed.
Lemma lem3996289 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : term630 A B f s x.
Proof. exact (@lem3996288 A B f s x). Qed.
Lemma lem3996290 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term630 A B f s x) = (term585 A B x f s).
Proof. exact (eq_refl (term630 A B f s x)). Qed.
Lemma lem3996291 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term585 A B x f s.
Proof. exact (EQ_MP (@lem3996290 A B x f s) (@lem3996289 A B f s x)). Qed.
Lemma lem3996293 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term585 A B x f s.
Proof. exact (@lem3992094 A B x f s (@lem3996291 A B x f s)). Qed.
Lemma lem3996294 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term48 A B f s) : term598 A B x f s.
Proof. exact (@lem3996293 A B x f s (@lem3971726 A B f s h1)). Qed.
Lemma lem3996295 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term124 A x s) (h2 : term48 A B f s) : term596 A B x f s.
Proof. exact (@lem3996294 A B x f s h2 (@lem3971728 A x s h1)). Qed.
Lemma lem3996296 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : term594 A B x f s.
Proof. exact (@lem3996295 A B x f s h2 h3 (@lem3971727 A s h1)). Qed.
Lemma lem3996297 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : term592 A B x f s.
Proof. exact (@lem3996296 A B x f s h2 h3 h4 (@lem3971729 A B f x s h1)). Qed.
Lemma lem3996298 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : term590 A B f s.
Proof. exact (@lem3996297 A B x f s h1 h2 h4 h5 (@lem3987319 A B x f s h3)). Qed.
Lemma lem3996299 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term584 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : term224 A B.
Proof. exact (@lem3996298 A B x f s h1 h2 h3 h5 h6 (@lem3992073 A B f s h4)). Qed.
Lemma lem3996300 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term584 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : term222 B.
Proof. exact (@lem3996299 A B x f s h1 h2 h3 h4 h5 h6 (@lem3992074 A)). Qed.
Lemma lem3996301 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term584 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : term219.
Proof. exact (@lem3996300 A B x f s h1 h2 h3 h4 h5 h6 (@lem3992076 B)). Qed.
Lemma lem3996302 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term584 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : False.
Proof. exact (@lem3996301 A B x f s h1 h2 h3 h4 h5 h6 (@lem3992078)). Qed.
Lemma lem3996303 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term584 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : (term584 A B f s) = False.
Proof. exact (prop_ext (fun h7 : term584 A B f s => @lem3996302 A B x f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3992073 A B f s h4)). Qed.
Lemma lem3996304 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term584 A B f s) (h5 : term124 A x s) (h6 : term48 A B f s) : False.
Proof. exact (EQ_MP (@lem3996303 A B x f s h1 h2 h3 h4 h5 h6) (@lem3992073 A B f s h4)). Qed.
Lemma lem3996305 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : term583 A B f s.
Proof. exact (fun h0 : term584 A B f s => @lem3996304 A B x f s h1 h2 h3 h0 h4 h5). Qed.
Lemma lem3996307 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term156 A B f s) = (term175 A s).
Proof. exact (EQ_MP (@lem3992072 A B f s) (@lem3996305 A B x f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3996308 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term170 A B x f s) = ((term156 A B f s) = (term175 A s)).
Proof. exact (prop_ext (fun h6 : term170 A B x f s => @lem3996307 A B x f s h1 h2 h3 h4 h5) (fun h6 : (term156 A B f s) = (term175 A s) => @lem3987319 A B x f s h3)). Qed.
Lemma lem3996309 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term170 A B x f s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term156 A B f s) = (term175 A s).
Proof. exact (EQ_MP (@lem3996308 A B x f s h1 h2 h3 h4 h5) (@lem3987319 A B x f s h3)). Qed.
Lemma lem3996310 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : term200 A B x f s.
Proof. exact (fun h0 : term170 A B x f s => @lem3996309 A B x f s h1 h2 h0 h3 h4). Qed.
Lemma lem3996311 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term32 A B f s) = (term175 A s).
Proof. exact (EQ_MP (@lem3987339 A B f s) (@lem3992067 A B x f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3996312 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term163 A B x f s) = ((term32 A B f s) = (term175 A s)).
Proof. exact (prop_ext (fun h6 : term163 A B x f s => @lem3996311 A B x f s h1 h2 h3 h4 h5) (fun h6 : (term32 A B f s) = (term175 A s) => @lem3987302 A B x f s h2)). Qed.
Lemma lem3996313 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : term163 A B x f s) (h3 : @FINITE A s) (h4 : term124 A x s) (h5 : term48 A B f s) : (term32 A B f s) = (term175 A s).
Proof. exact (EQ_MP (@lem3996312 A B x f s h1 h2 h3 h4 h5) (@lem3987302 A B x f s h2)). Qed.
Lemma lem3996314 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : term204 A B x f s.
Proof. exact (fun h0 : term163 A B x f s => @lem3996313 A B x f s h1 h0 h2 h3 h4). Qed.
Lemma lem3996315 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : term207 A B x f s.
Proof. exact (conj (@lem3996314 A B x f s h1 h2 h3 h4) (@lem3996310 A B x f s h1 h2 h3 h4)). Qed.
Lemma lem3996316 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : (term172 A B x f s) = (term175 A s).
Proof. exact (EQ_MP (@lem3987301 A B x f s) (@lem3996315 A B x f s h1 h2 h3 h4)). Qed.
Lemma lem3996317 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : (term112 A B x f s) = (term115 A x s).
Proof. exact (EQ_MP (@lem3987283 A B f x s h2 h3) (@lem3996316 A B x f s h1 h2 h3 h4)). Qed.
Lemma lem3996318 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : (term125 A B f x s) = ((term112 A B x f s) = (term115 A x s)).
Proof. exact (prop_ext (fun h5 : term125 A B f x s => @lem3996317 A B x f s h1 h2 h3 h4) (fun h5 : (term112 A B x f s) = (term115 A x s) => @lem3971729 A B f x s h1)). Qed.
Lemma lem3996319 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B f x s) (h2 : @FINITE A s) (h3 : term124 A x s) (h4 : term48 A B f s) : (term112 A B x f s) = (term115 A x s).
Proof. exact (EQ_MP (@lem3996318 A B x f s h1 h2 h3 h4) (@lem3971729 A B f x s h1)). Qed.
Lemma lem3996320 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : term117 A B f x s.
Proof. exact (fun h0 : term125 A B f x s => @lem3996319 A B x f s h0 h1 h2 h3). Qed.
Lemma lem3996321 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term66 A B f x s) : term64 A x s.
Proof. exact (proj2 (@lem3971724 A B f x s h1)). Qed.
Lemma lem3996322 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term66 A B f x s) : term48 A B f s.
Proof. exact (proj1 (@lem3971724 A B f x s h1)). Qed.
Lemma lem3996323 {A : Type'} (x : A) (s : A -> Prop) (h1 : term64 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem3971725 A x s h1)). Qed.
Lemma lem3996324 {A : Type'} (x : A) (s : A -> Prop) (h1 : term64 A x s) : term124 A x s.
Proof. exact (proj1 (@lem3971725 A x s h1)). Qed.
Lemma lem3996325 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : (@FINITE A s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3996320 A B x f s h1 h2 h3) (fun h4 : term117 A B f x s => @lem3971727 A s h1)). Qed.
Lemma lem3996326 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996325 A B x f s h1 h2 h3) (@lem3971727 A s h1)). Qed.
Lemma lem3996327 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : (term124 A x s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h4 : term124 A x s => @lem3996326 A B x f s h1 h2 h3) (fun h4 : term117 A B f x s => @lem3971728 A x s h2)). Qed.
Lemma lem3996328 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term124 A x s) (h3 : term48 A B f s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996327 A B x f s h1 h2 h3) (@lem3971728 A x s h2)). Qed.
Lemma lem3996329 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term124 A x s) (h2 : term64 A x s) (h3 : term48 A B f s) : (@FINITE A s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3996328 A B x f s h4 h1 h3) (fun h4 : term117 A B f x s => @lem3996323 A x s h2)). Qed.
Lemma lem3996330 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term124 A x s) (h2 : term64 A x s) (h3 : term48 A B f s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996329 A B x f s h1 h2 h3) (@lem3996323 A x s h2)). Qed.
Lemma lem3996331 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term64 A x s) (h2 : term48 A B f s) : (term124 A x s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h3 : term124 A x s => @lem3996330 A B x f s h3 h1 h2) (fun h3 : term117 A B f x s => @lem3996324 A x s h1)). Qed.
Lemma lem3996332 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term64 A x s) (h2 : term48 A B f s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996331 A B x f s h1 h2) (@lem3996324 A x s h1)). Qed.
Lemma lem3996333 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term64 A x s) (h2 : term48 A B f s) : (term48 A B f s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h3 : term48 A B f s => @lem3996332 A B x f s h1 h2) (fun h3 : term117 A B f x s => @lem3971726 A B f s h2)). Qed.
Lemma lem3996334 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term64 A x s) (h2 : term48 A B f s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996333 A B x f s h1 h2) (@lem3971726 A B f s h2)). Qed.
Lemma lem3996335 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term66 A B f x s) (h2 : term48 A B f s) : (term64 A x s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h3 : term64 A x s => @lem3996334 A B x f s h3 h2) (fun h3 : term117 A B f x s => @lem3996321 A B f x s h1)). Qed.
Lemma lem3996336 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term66 A B f x s) (h2 : term48 A B f s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996335 A B x f s h1 h2) (@lem3996321 A B f x s h1)). Qed.
Lemma lem3996337 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term66 A B f x s) : (term48 A B f s) = (term117 A B f x s).
Proof. exact (prop_ext (fun h2 : term48 A B f s => @lem3996336 A B x f s h1 h2) (fun h2 : term117 A B f x s => @lem3996322 A B f x s h1)). Qed.
Lemma lem3996338 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term66 A B f x s) : term117 A B f x s.
Proof. exact (EQ_MP (@lem3996337 A B f x s h1) (@lem3996322 A B f x s h1)). Qed.
Lemma lem3996339 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term118 A B f x s.
Proof. exact (fun h0 : term66 A B f x s => @lem3996338 A B f x s h0). Qed.
Lemma lem3996344 {A B : Type'} (f : A -> B) (x : A) : term120 A B f x.
Proof. exact (fun s : A -> Prop => @lem3996339 A B f x s). Qed.
Lemma lem3996349 {A B : Type'} (f : A -> B) : term122 A B f.
Proof. exact (fun x : A => @lem3996344 A B f x). Qed.
Lemma lem3996350 {A B : Type'} (f : A -> B) : term123 A B f.
Proof. exact (conj (@lem3971785 A B) (@lem3996349 A B f)). Qed.
Lemma lem3996351 {A B : Type'} (f : A -> B) : term82 A B f.
Proof. exact (EQ_MP (@lem3971723 A B f) (@lem3996350 A B f)). Qed.
Lemma lem3996352 {A B : Type'} (f : A -> B) : term54 A B f.
Proof. exact (@lem3971530 A B f (@lem3996351 A B f)). Qed.
Lemma lem3996353 {A B : Type'} (f : A -> B) : term53 A B f.
Proof. exact (EQ_MP (@lem3971497 A B f) (@lem3996352 A B f)). Qed.
Lemma lem3996358 {A B : Type'} : term631 A B.
Proof. exact (fun f : A -> B => @lem3996353 A B f). Qed.
