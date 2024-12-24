Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_CLAUSES_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm9523_spec.
Require Import thm9524_spec.
Lemma lem12310 {A : Type'} : (@COND A) = (term0 A).
Proof. exact (@COND_def A). Qed.
Lemma lem12318 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem12319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem12320 (t : Prop) : (term1 t) = (imp t).
Proof. exact (MK_COMB (@lem12319) (@lem12318 t)). Qed.
Lemma lem12323 {A : Type'} (x : A) (t1 : A) : (x = t1) = (x = t1).
Proof. exact (eq_refl (x = t1)). Qed.
Lemma lem12324 {A : Type'} (t : Prop) (x : A) (t1 : A) : (term2 A t x t1) = (term3 A t x t1).
Proof. exact (MK_COMB (@lem12320 t) (@lem12323 A x t1)). Qed.
Lemma lem12327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12328 {A : Type'} (t : Prop) (x : A) (t1 : A) : (term4 A t x t1) = (term5 A t x t1).
Proof. exact (MK_COMB (@lem12327) (@lem12324 A t x t1)). Qed.
Lemma lem12334 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem12335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem12336 (t : Prop) : (term6 t) = (term7 t).
Proof. exact (MK_COMB (@lem12335) (@lem12334 t)). Qed.
Lemma lem12339 {A : Type'} (x : A) (t2 : A) : (x = t2) = (x = t2).
Proof. exact (eq_refl (x = t2)). Qed.
Lemma lem12340 {A : Type'} (t : Prop) (x : A) (t2 : A) : (term8 A t x t2) = (term9 A t x t2).
Proof. exact (MK_COMB (@lem12336 t) (@lem12339 A x t2)). Qed.
Lemma lem12343 {A : Type'} (t1 : A) (t : Prop) (x : A) (t2 : A) : (term10 A t1 t x t2) = (term11 A t1 t x t2).
Proof. exact (MK_COMB (@lem12328 A t x t1) (@lem12340 A t x t2)). Qed.
Lemma lem12346 {A : Type'} (t1 : A) (t : Prop) (t2 : A) : (term12 A t1 t t2) = (term13 A t1 t t2).
Proof. exact (fun_ext (fun x : A => @lem12343 A t1 t x t2)). Qed.
Lemma lem12347 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem12348 {A : Type'} (t1 : A) (t : Prop) (t2 : A) : (term14 A t1 t t2) = (term15 A t1 t t2).
Proof. exact (MK_COMB (@lem12347 A) (@lem12346 A t1 t t2)). Qed.
Lemma lem12349 {A : Type'} (t1 : A) (t : Prop) : (term16 A t1 t) = (term17 A t1 t).
Proof. exact (fun_ext (fun t2 : A => @lem12348 A t1 t t2)). Qed.
Lemma lem12350 {A : Type'} (t : Prop) : (term18 A t) = (term19 A t).
Proof. exact (fun_ext (fun t1 : A => @lem12349 A t1 t)). Qed.
Lemma lem12351 {A : Type'} : (term0 A) = (term20 A).
Proof. exact (fun_ext (fun t : Prop => @lem12350 A t)). Qed.
Lemma lem12352 {A : Type'} : (@COND A) = (term20 A).
Proof. exact (TRANS (@lem12310 A) (@lem12351 A)). Qed.
Lemma lem12353 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem12354 {A : Type'} : (@COND A True) = (term21 A).
Proof. exact (MK_COMB (@lem12352 A) (@lem12353)). Qed.
Lemma lem12356 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem12357 {A : Type'} (f : type1537 A) (y : Prop) : (term23 A f y) = (f y).
Proof. exact (@lem12356 Prop (type1400 A) f y). Qed.
Lemma lem12358 {A : Type'} : (term24 A) = (term21 A).
Proof. exact (@lem12357 A (term20 A) True). Qed.
Lemma lem12359 {A : Type'} (t : Prop) : (term25 A t) = (term19 A t).
Proof. exact (eq_refl (term25 A t)). Qed.
Lemma lem12360 {A : Type'} : (term26 A) = (term20 A).
Proof. exact (fun_ext (fun t : Prop => @lem12359 A t)). Qed.
Lemma lem12361 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem12362 {A : Type'} : (term24 A) = (term21 A).
Proof. exact (MK_COMB (@lem12360 A) (@lem12361)). Qed.
Lemma lem12363 {A : Type'} : (@eq (A -> A -> A)) = (@eq (A -> A -> A)).
Proof. exact (eq_refl (@eq (A -> A -> A))). Qed.
Lemma lem12364 {A : Type'} : (term27 A) = (term28 A).
Proof. exact (MK_COMB (@lem12363 A) (@lem12362 A)). Qed.
Lemma lem12365 {A : Type'} : (term21 A) = (term29 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem12366 {A : Type'} : ((term24 A) = (term21 A)) = ((term21 A) = (term29 A)).
Proof. exact (MK_COMB (@lem12364 A) (@lem12365 A)). Qed.
Lemma lem12367 {A : Type'} : (term21 A) = (term29 A).
Proof. exact (EQ_MP (@lem12366 A) (@lem12358 A)). Qed.
Lemma lem12371 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem12372 {A : Type'} (x : A) (t1 : A) : (term30 A x t1) = (x = t1).
Proof. exact (@lem12371 (x = t1)). Qed.
Lemma lem12375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12376 {A : Type'} (x : A) (t1 : A) : (term31 A x t1) = (term32 A x t1).
Proof. exact (MK_COMB (@lem12375) (@lem12372 A x t1)). Qed.
Lemma lem12380 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem12381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem12382 : term33 = (imp False).
Proof. exact (MK_COMB (@lem12381) (@lem12380)). Qed.
Lemma lem12385 {A : Type'} (x : A) (t2 : A) : (x = t2) = (x = t2).
Proof. exact (eq_refl (x = t2)). Qed.
Lemma lem12386 {A : Type'} (x : A) (t2 : A) : (term34 A x t2) = (term35 A x t2).
Proof. exact (MK_COMB (@lem12382) (@lem12385 A x t2)). Qed.
Lemma lem12388 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem12389 {A : Type'} (x : A) (t2 : A) : (term35 A x t2) = True.
Proof. exact (@lem12388 (x = t2)). Qed.
Lemma lem12390 {A : Type'} (x : A) (t2 : A) : (term34 A x t2) = True.
Proof. exact (TRANS (@lem12386 A x t2) (@lem12389 A x t2)). Qed.
Lemma lem12391 {A : Type'} (t2 : A) (x : A) (t1 : A) : (term36 A t1 x t2) = (term37 A x t1).
Proof. exact (MK_COMB (@lem12376 A x t1) (@lem12390 A x t2)). Qed.
Lemma lem12393 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem12394 {A : Type'} (x : A) (t1 : A) : (term37 A x t1) = (x = t1).
Proof. exact (@lem12393 (x = t1)). Qed.
Lemma lem12397 {A : Type'} (t2 : A) (x : A) (t1 : A) : (term36 A t1 x t2) = (x = t1).
Proof. exact (TRANS (@lem12391 A t2 x t1) (@lem12394 A x t1)). Qed.
Lemma lem12398 {A : Type'} (t2 : A) (t1 : A) : (term38 A t1 t2) = (term39 A t1).
Proof. exact (fun_ext (fun x : A => @lem12397 A t2 x t1)). Qed.
Lemma lem12399 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem12400 {A : Type'} (t2 : A) (t1 : A) : (term40 A t1 t2) = (term41 A t1).
Proof. exact (MK_COMB (@lem12399 A) (@lem12398 A t2 t1)). Qed.
Lemma lem12402 {A : Type'} (x : A) : (term41 A x) = x.
Proof. exact (EQ_MP (@lem9524 A x) (@lem9523 A x)). Qed.
Lemma lem12403 {A : Type'} (x : A) : (term41 A x) = x.
Proof. exact (@lem12402 A x). Qed.
Lemma lem12404 {A : Type'} (t1 : A) : (term41 A t1) = t1.
Proof. exact (@lem12403 A t1). Qed.
Lemma lem12407 {A : Type'} (t1 : A) : (term42 A t1) = (term42 A t1).
Proof. exact (eq_refl (term42 A t1)). Qed.
Lemma lem12408 {A : Type'} (t1 : A) : (term42 A t1) = ((term41 A t1) = t1).
Proof. exact (eq_refl (term42 A t1)). Qed.
Lemma lem12409 {A : Type'} (t1 : A) : (term43 A t1) = (term43 A t1).
Proof. exact (eq_refl (term43 A t1)). Qed.
Lemma lem12410 {A : Type'} (t1 : A) : ((term42 A t1) = (term42 A t1)) = ((term42 A t1) = ((term41 A t1) = t1)).
Proof. exact (MK_COMB (@lem12409 A t1) (@lem12408 A t1)). Qed.
Lemma lem12411 {A : Type'} (t1 : A) : (term42 A t1) = ((term41 A t1) = t1).
Proof. exact (eq_refl (term42 A t1)). Qed.
Lemma lem12412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12413 {A : Type'} (t1 : A) : (term43 A t1) = (term44 A t1).
Proof. exact (MK_COMB (@lem12412) (@lem12411 A t1)). Qed.
Lemma lem12414 {A : Type'} (t1 : A) : ((term41 A t1) = t1) = ((term41 A t1) = t1).
Proof. exact (eq_refl ((term41 A t1) = t1)). Qed.
Lemma lem12415 {A : Type'} (t1 : A) : ((term42 A t1) = ((term41 A t1) = t1)) = (((term41 A t1) = t1) = ((term41 A t1) = t1)).
Proof. exact (MK_COMB (@lem12413 A t1) (@lem12414 A t1)). Qed.
Lemma lem12416 {A : Type'} (t1 : A) : ((term42 A t1) = (term42 A t1)) = (((term41 A t1) = t1) = ((term41 A t1) = t1)).
Proof. exact (TRANS (@lem12410 A t1) (@lem12415 A t1)). Qed.
Lemma lem12417 {A : Type'} (t1 : A) : ((term41 A t1) = t1) = ((term41 A t1) = t1).
Proof. exact (EQ_MP (@lem12416 A t1) (@lem12407 A t1)). Qed.
Lemma lem12418 {A : Type'} (t1 : A) : (term41 A t1) = t1.
Proof. exact (EQ_MP (@lem12417 A t1) (@lem12404 A t1)). Qed.
Lemma lem12419 {A : Type'} (t2 : A) (t1 : A) : (term40 A t1 t2) = t1.
Proof. exact (TRANS (@lem12400 A t2 t1) (@lem12418 A t1)). Qed.
Lemma lem12420 {A : Type'} (t1 : A) : (term45 A t1) = (term46 A t1).
Proof. exact (fun_ext (fun t2 : A => @lem12419 A t2 t1)). Qed.
Lemma lem12421 {A : Type'} : (term29 A) = (term47 A).
Proof. exact (fun_ext (fun t1 : A => @lem12420 A t1)). Qed.
Lemma lem12422 {A : Type'} : (term21 A) = (term47 A).
Proof. exact (TRANS (@lem12367 A) (@lem12421 A)). Qed.
Lemma lem12423 {A : Type'} : (@COND A True) = (term47 A).
Proof. exact (TRANS (@lem12354 A) (@lem12422 A)). Qed.
Lemma lem12424 {A : Type'} (t1 : A) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12425 {A : Type'} (t1 : A) : (@COND A True t1) = (term48 A t1).
Proof. exact (MK_COMB (@lem12423 A) (@lem12424 A t1)). Qed.
Lemma lem12427 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem12428 {A : Type'} (f : type1400 A) (y : A) : (term49 A f y) = (f y).
Proof. exact (@lem12427 A (A -> A) f y). Qed.
Lemma lem12429 {A : Type'} (t1 : A) : (term50 A t1) = (term48 A t1).
Proof. exact (@lem12428 A (term47 A) t1). Qed.
Lemma lem12430 {A : Type'} (t1 : A) : (term48 A t1) = (term46 A t1).
Proof. exact (eq_refl (term48 A t1)). Qed.
Lemma lem12431 {A : Type'} : (term51 A) = (term47 A).
Proof. exact (fun_ext (fun t1 : A => @lem12430 A t1)). Qed.
Lemma lem12432 {A : Type'} (t1 : A) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12433 {A : Type'} (t1 : A) : (term50 A t1) = (term48 A t1).
Proof. exact (MK_COMB (@lem12431 A) (@lem12432 A t1)). Qed.
Lemma lem12434 {A : Type'} : (@eq (A -> A)) = (@eq (A -> A)).
Proof. exact (eq_refl (@eq (A -> A))). Qed.
Lemma lem12435 {A : Type'} (t1 : A) : (term52 A t1) = (term53 A t1).
Proof. exact (MK_COMB (@lem12434 A) (@lem12433 A t1)). Qed.
Lemma lem12436 {A : Type'} (t1 : A) : (term48 A t1) = (term46 A t1).
Proof. exact (eq_refl (term48 A t1)). Qed.
Lemma lem12437 {A : Type'} (t1 : A) : ((term50 A t1) = (term48 A t1)) = ((term48 A t1) = (term46 A t1)).
Proof. exact (MK_COMB (@lem12435 A t1) (@lem12436 A t1)). Qed.
Lemma lem12438 {A : Type'} (t1 : A) : (term48 A t1) = (term46 A t1).
Proof. exact (EQ_MP (@lem12437 A t1) (@lem12429 A t1)). Qed.
Lemma lem12439 {A : Type'} (t1 : A) : (@COND A True t1) = (term46 A t1).
Proof. exact (TRANS (@lem12425 A t1) (@lem12438 A t1)). Qed.
Lemma lem12440 {A : Type'} (t2 : A) : t2 = t2.
Proof. exact (eq_refl t2). Qed.
Lemma lem12441 {A : Type'} (t1 : A) (t2 : A) : (@COND A True t1 t2) = (term54 A t1 t2).
Proof. exact (MK_COMB (@lem12439 A t1) (@lem12440 A t2)). Qed.
Lemma lem12443 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem12444 {A : Type'} (f : A -> A) (y : A) : (term55 A f y) = (f y).
Proof. exact (@lem12443 A A f y). Qed.
Lemma lem12445 {A : Type'} (t1 : A) (t2 : A) : (term56 A t1 t2) = (term54 A t1 t2).
Proof. exact (@lem12444 A (term46 A t1) t2). Qed.
Lemma lem12446 {A : Type'} (t2 : A) (t1 : A) : (term54 A t1 t2) = t1.
Proof. exact (eq_refl (term54 A t1 t2)). Qed.
Lemma lem12447 {A : Type'} (t1 : A) : (term57 A t1) = (term46 A t1).
Proof. exact (fun_ext (fun t2 : A => @lem12446 A t2 t1)). Qed.
Lemma lem12448 {A : Type'} (t2 : A) : t2 = t2.
Proof. exact (eq_refl t2). Qed.
Lemma lem12449 {A : Type'} (t1 : A) (t2 : A) : (term56 A t1 t2) = (term54 A t1 t2).
Proof. exact (MK_COMB (@lem12447 A t1) (@lem12448 A t2)). Qed.
Lemma lem12450 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem12451 {A : Type'} (t1 : A) (t2 : A) : (term58 A t1 t2) = (term59 A t1 t2).
Proof. exact (MK_COMB (@lem12450 A) (@lem12449 A t1 t2)). Qed.
Lemma lem12452 {A : Type'} (t2 : A) (t1 : A) : (term54 A t1 t2) = t1.
Proof. exact (eq_refl (term54 A t1 t2)). Qed.
Lemma lem12453 {A : Type'} (t2 : A) (t1 : A) : ((term56 A t1 t2) = (term54 A t1 t2)) = ((term54 A t1 t2) = t1).
Proof. exact (MK_COMB (@lem12451 A t1 t2) (@lem12452 A t2 t1)). Qed.
Lemma lem12454 {A : Type'} (t2 : A) (t1 : A) : (term54 A t1 t2) = t1.
Proof. exact (EQ_MP (@lem12453 A t2 t1) (@lem12445 A t1 t2)). Qed.
Lemma lem12455 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (TRANS (@lem12441 A t1 t2) (@lem12454 A t2 t1)). Qed.
Lemma lem12456 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem12457 {A : Type'} (t2 : A) (t1 : A) : (term60 A t1 t2) = (@eq A t1).
Proof. exact (MK_COMB (@lem12456 A) (@lem12455 A t2 t1)). Qed.
Lemma lem12458 {A : Type'} (t1 : A) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12459 {A : Type'} (t2 : A) (t1 : A) : ((@COND A True t1 t2) = t1) = (t1 = t1).
Proof. exact (MK_COMB (@lem12457 A t2 t1) (@lem12458 A t1)). Qed.
Lemma lem12461 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12462 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem12461 A x). Qed.
Lemma lem12463 {A : Type'} (t1 : A) : (t1 = t1) = True.
Proof. exact (@lem12462 A t1). Qed.
Lemma lem12464 {A : Type'} (t2 : A) (t1 : A) : ((@COND A True t1 t2) = t1) = True.
Proof. exact (TRANS (@lem12459 A t2 t1) (@lem12463 A t1)). Qed.
Lemma lem12465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12466 {A : Type'} (t2 : A) (t1 : A) : (term61 A t2 t1) = (and True).
Proof. exact (MK_COMB (@lem12465) (@lem12464 A t2 t1)). Qed.
Lemma lem12470 {A : Type'} : (@COND A) = (term0 A).
Proof. exact (@COND_def A). Qed.
Lemma lem12478 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem12479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem12480 (t : Prop) : (term1 t) = (imp t).
Proof. exact (MK_COMB (@lem12479) (@lem12478 t)). Qed.
Lemma lem12483 {A : Type'} (x : A) (t1 : A) : (x = t1) = (x = t1).
Proof. exact (eq_refl (x = t1)). Qed.
Lemma lem12484 {A : Type'} (t : Prop) (x : A) (t1 : A) : (term2 A t x t1) = (term3 A t x t1).
Proof. exact (MK_COMB (@lem12480 t) (@lem12483 A x t1)). Qed.
Lemma lem12487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12488 {A : Type'} (t : Prop) (x : A) (t1 : A) : (term4 A t x t1) = (term5 A t x t1).
Proof. exact (MK_COMB (@lem12487) (@lem12484 A t x t1)). Qed.
Lemma lem12494 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem12495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem12496 (t : Prop) : (term6 t) = (term7 t).
Proof. exact (MK_COMB (@lem12495) (@lem12494 t)). Qed.
Lemma lem12499 {A : Type'} (x : A) (t2 : A) : (x = t2) = (x = t2).
Proof. exact (eq_refl (x = t2)). Qed.
Lemma lem12500 {A : Type'} (t : Prop) (x : A) (t2 : A) : (term8 A t x t2) = (term9 A t x t2).
Proof. exact (MK_COMB (@lem12496 t) (@lem12499 A x t2)). Qed.
Lemma lem12503 {A : Type'} (t1 : A) (t : Prop) (x : A) (t2 : A) : (term10 A t1 t x t2) = (term11 A t1 t x t2).
Proof. exact (MK_COMB (@lem12488 A t x t1) (@lem12500 A t x t2)). Qed.
Lemma lem12506 {A : Type'} (t1 : A) (t : Prop) (t2 : A) : (term12 A t1 t t2) = (term13 A t1 t t2).
Proof. exact (fun_ext (fun x : A => @lem12503 A t1 t x t2)). Qed.
Lemma lem12507 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem12508 {A : Type'} (t1 : A) (t : Prop) (t2 : A) : (term14 A t1 t t2) = (term15 A t1 t t2).
Proof. exact (MK_COMB (@lem12507 A) (@lem12506 A t1 t t2)). Qed.
Lemma lem12509 {A : Type'} (t1 : A) (t : Prop) : (term16 A t1 t) = (term17 A t1 t).
Proof. exact (fun_ext (fun t2 : A => @lem12508 A t1 t t2)). Qed.
Lemma lem12510 {A : Type'} (t : Prop) : (term18 A t) = (term19 A t).
Proof. exact (fun_ext (fun t1 : A => @lem12509 A t1 t)). Qed.
Lemma lem12511 {A : Type'} : (term0 A) = (term20 A).
Proof. exact (fun_ext (fun t : Prop => @lem12510 A t)). Qed.
Lemma lem12512 {A : Type'} : (@COND A) = (term20 A).
Proof. exact (TRANS (@lem12470 A) (@lem12511 A)). Qed.
Lemma lem12513 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem12514 {A : Type'} : (@COND A False) = (term62 A).
Proof. exact (MK_COMB (@lem12512 A) (@lem12513)). Qed.
Lemma lem12516 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem12517 {A : Type'} (f : type1537 A) (y : Prop) : (term23 A f y) = (f y).
Proof. exact (@lem12516 Prop (type1400 A) f y). Qed.
Lemma lem12518 {A : Type'} : (term63 A) = (term62 A).
Proof. exact (@lem12517 A (term20 A) False). Qed.
Lemma lem12519 {A : Type'} (t : Prop) : (term25 A t) = (term19 A t).
Proof. exact (eq_refl (term25 A t)). Qed.
Lemma lem12520 {A : Type'} : (term26 A) = (term20 A).
Proof. exact (fun_ext (fun t : Prop => @lem12519 A t)). Qed.
Lemma lem12521 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem12522 {A : Type'} : (term63 A) = (term62 A).
Proof. exact (MK_COMB (@lem12520 A) (@lem12521)). Qed.
Lemma lem12523 {A : Type'} : (@eq (A -> A -> A)) = (@eq (A -> A -> A)).
Proof. exact (eq_refl (@eq (A -> A -> A))). Qed.
Lemma lem12524 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (MK_COMB (@lem12523 A) (@lem12522 A)). Qed.
Lemma lem12525 {A : Type'} : (term62 A) = (term66 A).
Proof. exact (eq_refl (term62 A)). Qed.
Lemma lem12526 {A : Type'} : ((term63 A) = (term62 A)) = ((term62 A) = (term66 A)).
Proof. exact (MK_COMB (@lem12524 A) (@lem12525 A)). Qed.
Lemma lem12527 {A : Type'} : (term62 A) = (term66 A).
Proof. exact (EQ_MP (@lem12526 A) (@lem12518 A)). Qed.
Lemma lem12531 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem12532 {A : Type'} (x : A) (t1 : A) : (term35 A x t1) = True.
Proof. exact (@lem12531 (x = t1)). Qed.
Lemma lem12533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12534 {A : Type'} (x : A) (t1 : A) : (term67 A x t1) = (and True).
Proof. exact (MK_COMB (@lem12533) (@lem12532 A x t1)). Qed.
Lemma lem12538 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem12539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem12540 : term68 = (imp True).
Proof. exact (MK_COMB (@lem12539) (@lem12538)). Qed.
Lemma lem12543 {A : Type'} (x : A) (t2 : A) : (x = t2) = (x = t2).
Proof. exact (eq_refl (x = t2)). Qed.
Lemma lem12544 {A : Type'} (x : A) (t2 : A) : (term69 A x t2) = (term30 A x t2).
Proof. exact (MK_COMB (@lem12540) (@lem12543 A x t2)). Qed.
Lemma lem12546 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem12547 {A : Type'} (x : A) (t2 : A) : (term30 A x t2) = (x = t2).
Proof. exact (@lem12546 (x = t2)). Qed.
Lemma lem12550 {A : Type'} (x : A) (t2 : A) : (term69 A x t2) = (x = t2).
Proof. exact (TRANS (@lem12544 A x t2) (@lem12547 A x t2)). Qed.
Lemma lem12551 {A : Type'} (t1 : A) (x : A) (t2 : A) : (term70 A t1 x t2) = (term71 A x t2).
Proof. exact (MK_COMB (@lem12534 A x t1) (@lem12550 A x t2)). Qed.
Lemma lem12553 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem12554 {A : Type'} (x : A) (t2 : A) : (term71 A x t2) = (x = t2).
Proof. exact (@lem12553 (x = t2)). Qed.
Lemma lem12557 {A : Type'} (t1 : A) (x : A) (t2 : A) : (term70 A t1 x t2) = (x = t2).
Proof. exact (TRANS (@lem12551 A t1 x t2) (@lem12554 A x t2)). Qed.
Lemma lem12558 {A : Type'} (t1 : A) (t2 : A) : (term72 A t1 t2) = (term39 A t2).
Proof. exact (fun_ext (fun x : A => @lem12557 A t1 x t2)). Qed.
Lemma lem12559 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem12560 {A : Type'} (t1 : A) (t2 : A) : (term73 A t1 t2) = (term41 A t2).
Proof. exact (MK_COMB (@lem12559 A) (@lem12558 A t1 t2)). Qed.
Lemma lem12562 {A : Type'} (x : A) : (term41 A x) = x.
Proof. exact (EQ_MP (@lem9524 A x) (@lem9523 A x)). Qed.
Lemma lem12563 {A : Type'} (x : A) : (term41 A x) = x.
Proof. exact (@lem12562 A x). Qed.
Lemma lem12564 {A : Type'} (t2 : A) : (term41 A t2) = t2.
Proof. exact (@lem12563 A t2). Qed.
Lemma lem12567 {A : Type'} (t2 : A) : (term42 A t2) = (term42 A t2).
Proof. exact (eq_refl (term42 A t2)). Qed.
Lemma lem12568 {A : Type'} (t2 : A) : (term42 A t2) = ((term41 A t2) = t2).
Proof. exact (eq_refl (term42 A t2)). Qed.
Lemma lem12569 {A : Type'} (t2 : A) : (term43 A t2) = (term43 A t2).
Proof. exact (eq_refl (term43 A t2)). Qed.
Lemma lem12570 {A : Type'} (t2 : A) : ((term42 A t2) = (term42 A t2)) = ((term42 A t2) = ((term41 A t2) = t2)).
Proof. exact (MK_COMB (@lem12569 A t2) (@lem12568 A t2)). Qed.
Lemma lem12571 {A : Type'} (t2 : A) : (term42 A t2) = ((term41 A t2) = t2).
Proof. exact (eq_refl (term42 A t2)). Qed.
Lemma lem12572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12573 {A : Type'} (t2 : A) : (term43 A t2) = (term44 A t2).
Proof. exact (MK_COMB (@lem12572) (@lem12571 A t2)). Qed.
Lemma lem12574 {A : Type'} (t2 : A) : ((term41 A t2) = t2) = ((term41 A t2) = t2).
Proof. exact (eq_refl ((term41 A t2) = t2)). Qed.
Lemma lem12575 {A : Type'} (t2 : A) : ((term42 A t2) = ((term41 A t2) = t2)) = (((term41 A t2) = t2) = ((term41 A t2) = t2)).
Proof. exact (MK_COMB (@lem12573 A t2) (@lem12574 A t2)). Qed.
Lemma lem12576 {A : Type'} (t2 : A) : ((term42 A t2) = (term42 A t2)) = (((term41 A t2) = t2) = ((term41 A t2) = t2)).
Proof. exact (TRANS (@lem12570 A t2) (@lem12575 A t2)). Qed.
Lemma lem12577 {A : Type'} (t2 : A) : ((term41 A t2) = t2) = ((term41 A t2) = t2).
Proof. exact (EQ_MP (@lem12576 A t2) (@lem12567 A t2)). Qed.
Lemma lem12578 {A : Type'} (t2 : A) : (term41 A t2) = t2.
Proof. exact (EQ_MP (@lem12577 A t2) (@lem12564 A t2)). Qed.
Lemma lem12579 {A : Type'} (t1 : A) (t2 : A) : (term73 A t1 t2) = t2.
Proof. exact (TRANS (@lem12560 A t1 t2) (@lem12578 A t2)). Qed.
Lemma lem12580 {A : Type'} (t1 : A) : (term74 A t1) = (term75 A).
Proof. exact (fun_ext (fun t2 : A => @lem12579 A t1 t2)). Qed.
Lemma lem12581 {A : Type'} : (term66 A) = (term76 A).
Proof. exact (fun_ext (fun t1 : A => @lem12580 A t1)). Qed.
Lemma lem12582 {A : Type'} : (term62 A) = (term76 A).
Proof. exact (TRANS (@lem12527 A) (@lem12581 A)). Qed.
Lemma lem12583 {A : Type'} : (@COND A False) = (term76 A).
Proof. exact (TRANS (@lem12514 A) (@lem12582 A)). Qed.
Lemma lem12584 {A : Type'} (t1 : A) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12585 {A : Type'} (t1 : A) : (@COND A False t1) = (term77 A t1).
Proof. exact (MK_COMB (@lem12583 A) (@lem12584 A t1)). Qed.
Lemma lem12587 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem12588 {A : Type'} (f : type1400 A) (y : A) : (term49 A f y) = (f y).
Proof. exact (@lem12587 A (A -> A) f y). Qed.
Lemma lem12589 {A : Type'} (t1 : A) : (term78 A t1) = (term77 A t1).
Proof. exact (@lem12588 A (term76 A) t1). Qed.
Lemma lem12590 {A : Type'} (t1 : A) : (term77 A t1) = (term75 A).
Proof. exact (eq_refl (term77 A t1)). Qed.
Lemma lem12591 {A : Type'} : (term79 A) = (term76 A).
Proof. exact (fun_ext (fun t1 : A => @lem12590 A t1)). Qed.
Lemma lem12592 {A : Type'} (t1 : A) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12593 {A : Type'} (t1 : A) : (term78 A t1) = (term77 A t1).
Proof. exact (MK_COMB (@lem12591 A) (@lem12592 A t1)). Qed.
Lemma lem12594 {A : Type'} : (@eq (A -> A)) = (@eq (A -> A)).
Proof. exact (eq_refl (@eq (A -> A))). Qed.
Lemma lem12595 {A : Type'} (t1 : A) : (term80 A t1) = (term81 A t1).
Proof. exact (MK_COMB (@lem12594 A) (@lem12593 A t1)). Qed.
Lemma lem12596 {A : Type'} (t1 : A) : (term77 A t1) = (term75 A).
Proof. exact (eq_refl (term77 A t1)). Qed.
Lemma lem12597 {A : Type'} (t1 : A) : ((term78 A t1) = (term77 A t1)) = ((term77 A t1) = (term75 A)).
Proof. exact (MK_COMB (@lem12595 A t1) (@lem12596 A t1)). Qed.
Lemma lem12598 {A : Type'} (t1 : A) : (term77 A t1) = (term75 A).
Proof. exact (EQ_MP (@lem12597 A t1) (@lem12589 A t1)). Qed.
Lemma lem12599 {A : Type'} (t1 : A) : (@COND A False t1) = (term75 A).
Proof. exact (TRANS (@lem12585 A t1) (@lem12598 A t1)). Qed.
Lemma lem12600 {A : Type'} (t2 : A) : t2 = t2.
Proof. exact (eq_refl t2). Qed.
Lemma lem12601 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = (term82 A t2).
Proof. exact (MK_COMB (@lem12599 A t1) (@lem12600 A t2)). Qed.
Lemma lem12603 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem12604 {A : Type'} (f : A -> A) (y : A) : (term55 A f y) = (f y).
Proof. exact (@lem12603 A A f y). Qed.
Lemma lem12605 {A : Type'} (t2 : A) : (term83 A t2) = (term82 A t2).
Proof. exact (@lem12604 A (term75 A) t2). Qed.
Lemma lem12606 {A : Type'} (t2 : A) : (term82 A t2) = t2.
Proof. exact (eq_refl (term82 A t2)). Qed.
Lemma lem12607 {A : Type'} : (term84 A) = (term75 A).
Proof. exact (fun_ext (fun t2 : A => @lem12606 A t2)). Qed.
Lemma lem12608 {A : Type'} (t2 : A) : t2 = t2.
Proof. exact (eq_refl t2). Qed.
Lemma lem12609 {A : Type'} (t2 : A) : (term83 A t2) = (term82 A t2).
Proof. exact (MK_COMB (@lem12607 A) (@lem12608 A t2)). Qed.
Lemma lem12610 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem12611 {A : Type'} (t2 : A) : (term85 A t2) = (term86 A t2).
Proof. exact (MK_COMB (@lem12610 A) (@lem12609 A t2)). Qed.
Lemma lem12612 {A : Type'} (t2 : A) : (term82 A t2) = t2.
Proof. exact (eq_refl (term82 A t2)). Qed.
Lemma lem12613 {A : Type'} (t2 : A) : ((term83 A t2) = (term82 A t2)) = ((term82 A t2) = t2).
Proof. exact (MK_COMB (@lem12611 A t2) (@lem12612 A t2)). Qed.
Lemma lem12614 {A : Type'} (t2 : A) : (term82 A t2) = t2.
Proof. exact (EQ_MP (@lem12613 A t2) (@lem12605 A t2)). Qed.
Lemma lem12615 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (TRANS (@lem12601 A t1 t2) (@lem12614 A t2)). Qed.
Lemma lem12616 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem12617 {A : Type'} (t1 : A) (t2 : A) : (term87 A t1 t2) = (@eq A t2).
Proof. exact (MK_COMB (@lem12616 A) (@lem12615 A t1 t2)). Qed.
Lemma lem12618 {A : Type'} (t2 : A) : t2 = t2.
Proof. exact (eq_refl t2). Qed.
Lemma lem12619 {A : Type'} (t1 : A) (t2 : A) : ((@COND A False t1 t2) = t2) = (t2 = t2).
Proof. exact (MK_COMB (@lem12617 A t1 t2) (@lem12618 A t2)). Qed.
Lemma lem12621 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem12621 A x). Qed.
Lemma lem12623 {A : Type'} (t2 : A) : (t2 = t2) = True.
Proof. exact (@lem12622 A t2). Qed.
Lemma lem12624 {A : Type'} (t1 : A) (t2 : A) : ((@COND A False t1 t2) = t2) = True.
Proof. exact (TRANS (@lem12619 A t1 t2) (@lem12623 A t2)). Qed.
Lemma lem12625 {A : Type'} (t1 : A) (t2 : A) : (term88 A t1 t2) = (True /\ True).
Proof. exact (MK_COMB (@lem12466 A t2 t1) (@lem12624 A t1 t2)). Qed.
Lemma lem12627 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem12628 : (True /\ True) = True.
Proof. exact (@lem12627 True). Qed.
Lemma lem12629 {A : Type'} (t1 : A) (t2 : A) : (term88 A t1 t2) = True.
Proof. exact (TRANS (@lem12625 A t1 t2) (@lem12628)). Qed.
Lemma lem12630 {A : Type'} (t1 : A) : (term89 A t1) = (term90 A).
Proof. exact (fun_ext (fun t2 : A => @lem12629 A t1 t2)). Qed.
Lemma lem12631 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem12632 {A : Type'} (t1 : A) : (term91 A t1) = (term92 A).
Proof. exact (MK_COMB (@lem12631 A) (@lem12630 A t1)). Qed.
Lemma lem12634 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem12635 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem12634 A t). Qed.
Lemma lem12636 {A : Type'} : (term92 A) = True.
Proof. exact (@lem12635 A True). Qed.
Lemma lem12637 {A : Type'} (t1 : A) : (term91 A t1) = True.
Proof. exact (TRANS (@lem12632 A t1) (@lem12636 A)). Qed.
Lemma lem12638 {A : Type'} : (term94 A) = (term90 A).
Proof. exact (fun_ext (fun t1 : A => @lem12637 A t1)). Qed.
Lemma lem12639 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem12640 {A : Type'} : (term95 A) = (term92 A).
Proof. exact (MK_COMB (@lem12639 A) (@lem12638 A)). Qed.
Lemma lem12642 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem12643 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem12642 A t). Qed.
Lemma lem12644 {A : Type'} : (term92 A) = True.
Proof. exact (@lem12643 A True). Qed.
Lemma lem12645 {A : Type'} : (term95 A) = True.
Proof. exact (TRANS (@lem12640 A) (@lem12644 A)). Qed.
Lemma lem12646 {A : Type'} : True = (term95 A).
Proof. exact (SYM (@lem12645 A)). Qed.
Lemma lem12647 {A : Type'} : term95 A.
Proof. exact (EQ_MP (@lem12646 A) (@lem0)). Qed.
