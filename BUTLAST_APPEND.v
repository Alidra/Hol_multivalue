Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BUTLAST_APPEND_term_abbrevs.
Require Import APPEND_EQ_NIL_spec.
Require Import APPEND_NIL_spec.
Require Import COND_RAND_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1098923_spec.
Require Import thm1098924_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1200333 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1200334 (p : Prop) (q : Prop) : ((@COND Prop p True q) = (term1 p q)) = (term2 p q).
Proof. exact (@lem1200333 ((@COND Prop p True q) = (term1 p q))). Qed.
Lemma lem1200335 (p : Prop) (q : Prop) : (term2 p q) = ((@COND Prop p True q) = (term1 p q)).
Proof. exact (SYM (@lem1200334 p q)). Qed.
Lemma lem1200336 (p : Prop) (q : Prop) (h1 : term3 p q) : term3 p q.
Proof. exact (h1). Qed.
Lemma lem1200339 (p : Prop) (q : Prop) (h1 : term2 p q) : term2 p q.
Proof. exact (h1). Qed.
Lemma lem1200340 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun h0 : term2 p q => @lem1200339 p q h0). Qed.
Lemma lem1200341 (p : Prop) (q : Prop) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem1200342 (p : Prop) (q : Prop) (h1 : term2 p q) : term2 p q.
Proof. exact (h1). Qed.
Lemma lem1200343 (p : Prop) (q : Prop) (h1 : term2 p q) (h2 : term4 p q) : term2 p q.
Proof. exact (@lem1200341 p q h2 (@lem1200342 p q h1)). Qed.
Lemma lem1200344 (p : Prop) (q : Prop) (h1 : term2 p q) : term5 p q.
Proof. exact (fun h0 : term4 p q => @lem1200343 p q h1 h0). Qed.
Lemma lem1200345 (p : Prop) (q : Prop) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem1200346 (p : Prop) (q : Prop) (h1 : term2 p q) (h2 : term4 p q) : term2 p q.
Proof. exact (@lem1200344 p q h1 (@lem1200345 p q h2)). Qed.
Lemma lem1200347 (p : Prop) (q : Prop) (h1 : term4 p q) : term4 p q.
Proof. exact (fun h0 : term2 p q => @lem1200346 p q h0 h1). Qed.
Lemma lem1200348 (p : Prop) (q : Prop) : term6 p q.
Proof. exact (fun h0 : term4 p q => @lem1200347 p q h0). Qed.
Lemma lem1200351 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (@lem1200348 p q (@lem1200340 p q)). Qed.
Lemma lem1200361 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1200362 (p : Prop) (q : Prop) : (term2 p q) = (term7 p q).
Proof. exact (@lem1200361 (term3 p q)). Qed.
Lemma lem1200364 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1200365 (p : Prop) (q : Prop) : (term7 p q) = ((@COND Prop p True q) = (term1 p q)).
Proof. exact (@lem1200364 ((@COND Prop p True q) = (term1 p q))). Qed.
Lemma lem1200366 (p : Prop) (q : Prop) : (term2 p q) = ((@COND Prop p True q) = (term1 p q)).
Proof. exact (TRANS (@lem1200362 p q) (@lem1200365 p q)). Qed.
Lemma lem1200369 (q : Prop) : (term9 q) = (term10 q).
Proof. exact (fun_ext (fun p : Prop => @lem1200366 p q)). Qed.
Lemma lem1200370 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1200371 (q : Prop) : (term11 q) = (term12 q).
Proof. exact (MK_COMB (@lem1200370) (@lem1200369 q)). Qed.
Lemma lem1200376 : term13 = term14.
Proof. exact (fun_ext (fun q : Prop => @lem1200371 q)). Qed.
Lemma lem1200377 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1200386 : term15 = term16.
Proof. exact (MK_COMB (@lem1200377) (@lem1200376)). Qed.
Lemma lem1200390 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem1200391 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem1200392 (p : Prop) (h1 : p = False) : (@COND Prop p) = (@COND Prop False).
Proof. exact (MK_COMB (@lem1200391) (@lem1200390 p h1)). Qed.
Lemma lem1200393 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1200394 (p : Prop) (h1 : p = False) : (@COND Prop p True) = (@COND Prop False True).
Proof. exact (MK_COMB (@lem1200392 p h1) (@lem1200393)). Qed.
Lemma lem1200395 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem1200396 (q : Prop) (p : Prop) (h1 : p = False) : (@COND Prop p True q) = (@COND Prop False True q).
Proof. exact (MK_COMB (@lem1200394 p h1) (@lem1200395 q)). Qed.
Lemma lem1200398 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1200399 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem1200398 Prop t1 t2). Qed.
Lemma lem1200400 (q : Prop) : (@COND Prop False True q) = q.
Proof. exact (@lem1200399 True q). Qed.
Lemma lem1200401 (q : Prop) (p : Prop) (h1 : p = False) : (@COND Prop p True q) = q.
Proof. exact (TRANS (@lem1200396 q p h1) (@lem1200400 q)). Qed.
Lemma lem1200402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1200403 (q : Prop) (p : Prop) (h1 : p = False) : (term17 p q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem1200402) (@lem1200401 q p h1)). Qed.
Lemma lem1200405 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem1200406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1200407 (p : Prop) (h1 : p = False) : (~ p) = (~ False).
Proof. exact (MK_COMB (@lem1200406) (@lem1200405 p h1)). Qed.
Lemma lem1200409 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1200410 (p : Prop) (h1 : p = False) : (~ p) = True.
Proof. exact (TRANS (@lem1200407 p h1) (@lem1200409)). Qed.
Lemma lem1200411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1200412 (p : Prop) (h1 : p = False) : (term18 p) = (imp True).
Proof. exact (MK_COMB (@lem1200411) (@lem1200410 p h1)). Qed.
Lemma lem1200413 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem1200414 (q : Prop) (p : Prop) (h1 : p = False) : (term1 p q) = (True -> q).
Proof. exact (MK_COMB (@lem1200412 p h1) (@lem1200413 q)). Qed.
Lemma lem1200416 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1200417 (q : Prop) : (True -> q) = q.
Proof. exact (@lem1200416 q). Qed.
Lemma lem1200418 (q : Prop) (p : Prop) (h1 : p = False) : (term1 p q) = q.
Proof. exact (TRANS (@lem1200414 q p h1) (@lem1200417 q)). Qed.
Lemma lem1200419 (q : Prop) (p : Prop) (h1 : p = False) : ((@COND Prop p True q) = (term1 p q)) = (q = q).
Proof. exact (MK_COMB (@lem1200403 q p h1) (@lem1200418 q p h1)). Qed.
Lemma lem1200421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200422 (x : Prop) : (x = x) = True.
Proof. exact (@lem1200421 Prop x). Qed.
Lemma lem1200423 (q : Prop) : (q = q) = True.
Proof. exact (@lem1200422 q). Qed.
Lemma lem1200424 (q : Prop) (p : Prop) (h1 : p = False) : ((@COND Prop p True q) = (term1 p q)) = True.
Proof. exact (TRANS (@lem1200419 q p h1) (@lem1200423 q)). Qed.
Lemma lem1200425 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun h0 : p = False => @lem1200424 q p h0). Qed.
Lemma lem1200427 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem1200428 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem1200429 (p : Prop) (h1 : p = True) : (@COND Prop p) = (@COND Prop True).
Proof. exact (MK_COMB (@lem1200428) (@lem1200427 p h1)). Qed.
Lemma lem1200430 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1200431 (p : Prop) (h1 : p = True) : (@COND Prop p True) = (@COND Prop True True).
Proof. exact (MK_COMB (@lem1200429 p h1) (@lem1200430)). Qed.
Lemma lem1200432 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem1200433 (q : Prop) (p : Prop) (h1 : p = True) : (@COND Prop p True q) = (@COND Prop True True q).
Proof. exact (MK_COMB (@lem1200431 p h1) (@lem1200432 q)). Qed.
Lemma lem1200435 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1200436 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem1200435 Prop t2 t1). Qed.
Lemma lem1200437 (q : Prop) : (@COND Prop True True q) = True.
Proof. exact (@lem1200436 q True). Qed.
Lemma lem1200438 (q : Prop) (p : Prop) (h1 : p = True) : (@COND Prop p True q) = True.
Proof. exact (TRANS (@lem1200433 q p h1) (@lem1200437 q)). Qed.
Lemma lem1200439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1200440 (q : Prop) (p : Prop) (h1 : p = True) : (term17 p q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1200439) (@lem1200438 q p h1)). Qed.
Lemma lem1200442 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem1200443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1200444 (p : Prop) (h1 : p = True) : (~ p) = (~ True).
Proof. exact (MK_COMB (@lem1200443) (@lem1200442 p h1)). Qed.
Lemma lem1200446 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1200447 (p : Prop) (h1 : p = True) : (~ p) = False.
Proof. exact (TRANS (@lem1200444 p h1) (@lem1200446)). Qed.
Lemma lem1200448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1200449 (p : Prop) (h1 : p = True) : (term18 p) = (imp False).
Proof. exact (MK_COMB (@lem1200448) (@lem1200447 p h1)). Qed.
Lemma lem1200450 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem1200451 (q : Prop) (p : Prop) (h1 : p = True) : (term1 p q) = (False -> q).
Proof. exact (MK_COMB (@lem1200449 p h1) (@lem1200450 q)). Qed.
Lemma lem1200453 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1200454 (q : Prop) : (False -> q) = True.
Proof. exact (@lem1200453 q). Qed.
Lemma lem1200455 (q : Prop) (p : Prop) (h1 : p = True) : (term1 p q) = True.
Proof. exact (TRANS (@lem1200451 q p h1) (@lem1200454 q)). Qed.
Lemma lem1200456 (q : Prop) (p : Prop) (h1 : p = True) : ((@COND Prop p True q) = (term1 p q)) = (True = True).
Proof. exact (MK_COMB (@lem1200440 q p h1) (@lem1200455 q p h1)). Qed.
Lemma lem1200458 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1200459 : (True = True) = True.
Proof. exact (@lem1200458 True). Qed.
Lemma lem1200460 (q : Prop) (p : Prop) (h1 : p = True) : ((@COND Prop p True q) = (term1 p q)) = True.
Proof. exact (TRANS (@lem1200456 q p h1) (@lem1200459)). Qed.
Lemma lem1200461 (p : Prop) (q : Prop) : term20 p q.
Proof. exact (fun h0 : p = True => @lem1200460 q p h0). Qed.
Lemma lem1200462 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (conj (@lem1200425 p q) (@lem1200461 p q)). Qed.
Lemma lem1200464 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term22 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1200465 (q : Prop) (p : Prop) : term23 q p.
Proof. exact (@lem1200464 ((@COND Prop p True q) = (term1 p q)) True p True). Qed.
Lemma lem1200466 (q : Prop) (p : Prop) : ((@COND Prop p True q) = (term1 p q)) = (term24 p).
Proof. exact (@lem1200465 q p (@lem1200462 p q)). Qed.
Lemma lem1200468 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1200469 (p : Prop) : (p \/ True) = True.
Proof. exact (@lem1200468 p). Qed.
Lemma lem1200471 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1200472 (p : Prop) : (term25 p) = True.
Proof. exact (@lem1200471 (~ p)). Qed.
Lemma lem1200473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1200474 (p : Prop) : (term26 p) = (and True).
Proof. exact (MK_COMB (@lem1200473) (@lem1200472 p)). Qed.
Lemma lem1200475 (p : Prop) : (term24 p) = (True /\ True).
Proof. exact (MK_COMB (@lem1200474 p) (@lem1200469 p)). Qed.
Lemma lem1200477 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1200478 : (True /\ True) = True.
Proof. exact (@lem1200477 True). Qed.
Lemma lem1200479 (p : Prop) : (term24 p) = True.
Proof. exact (TRANS (@lem1200475 p) (@lem1200478)). Qed.
Lemma lem1200484 (p : Prop) (q : Prop) : ((@COND Prop p True q) = (term1 p q)) = True.
Proof. exact (TRANS (@lem1200466 q p) (@lem1200479 p)). Qed.
Lemma lem1200485 (q : Prop) : (term10 q) = term27.
Proof. exact (fun_ext (fun p : Prop => @lem1200484 p q)). Qed.
Lemma lem1200486 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1200487 (q : Prop) : (term12 q) = term28.
Proof. exact (MK_COMB (@lem1200486) (@lem1200485 q)). Qed.
Lemma lem1200488 : term14 = term29.
Proof. exact (fun_ext (fun q : Prop => @lem1200487 q)). Qed.
Lemma lem1200489 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1200490 : term16 = term30.
Proof. exact (MK_COMB (@lem1200489) (@lem1200488)). Qed.
Lemma lem1200491 : term15 = term30.
Proof. exact (TRANS (@lem1200386) (@lem1200490)). Qed.
Lemma lem1200493 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem1200494 (t : Prop) : (term32 t) = t.
Proof. exact (@lem1200493 Prop t). Qed.
Lemma lem1200495 : term30 = term28.
Proof. exact (@lem1200494 term28). Qed.
Lemma lem1200497 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem1200498 (t : Prop) : (term32 t) = t.
Proof. exact (@lem1200497 Prop t). Qed.
Lemma lem1200499 : term28 = True.
Proof. exact (@lem1200498 True). Qed.
Lemma lem1200500 : term30 = True.
Proof. exact (TRANS (@lem1200495) (@lem1200499)). Qed.
Lemma lem1200501 : term15 = True.
Proof. exact (TRANS (@lem1200491) (@lem1200500)). Qed.
Lemma lem1200502 : True = term15.
Proof. exact (SYM (@lem1200501)). Qed.
Lemma lem1200503 : term15.
Proof. exact (EQ_MP (@lem1200502) (@lem0)). Qed.
Lemma lem1200504 (q : Prop) : term33 q.
Proof. exact (@lem1200503 q). Qed.
Lemma lem1200505 (q : Prop) : (term33 q) = (term11 q).
Proof. exact (eq_refl (term33 q)). Qed.
Lemma lem1200506 (q : Prop) : term11 q.
Proof. exact (EQ_MP (@lem1200505 q) (@lem1200504 q)). Qed.
Lemma lem1200507 (q : Prop) (p : Prop) : term34 q p.
Proof. exact (@lem1200506 q p). Qed.
Lemma lem1200508 (p : Prop) (q : Prop) : (term34 q p) = (term2 p q).
Proof. exact (eq_refl (term34 q p)). Qed.
Lemma lem1200509 (p : Prop) (q : Prop) : term2 p q.
Proof. exact (EQ_MP (@lem1200508 p q) (@lem1200507 q p)). Qed.
Lemma lem1200511 (p : Prop) (q : Prop) : term2 p q.
Proof. exact (@lem1200351 p q (@lem1200509 p q)). Qed.
Lemma lem1200512 (p : Prop) (q : Prop) (h1 : term3 p q) : False.
Proof. exact (@lem1200511 p q (@lem1200336 p q h1)). Qed.
Lemma lem1200513 (p : Prop) (q : Prop) (h1 : term3 p q) : (term3 p q) = False.
Proof. exact (prop_ext (fun h2 : term3 p q => @lem1200512 p q h1) (fun h2 : False => @lem1200336 p q h1)). Qed.
Lemma lem1200514 (p : Prop) (q : Prop) (h1 : term3 p q) : False.
Proof. exact (EQ_MP (@lem1200513 p q h1) (@lem1200336 p q h1)). Qed.
Lemma lem1200515 (p : Prop) (q : Prop) : term2 p q.
Proof. exact (fun h0 : term3 p q => @lem1200514 p q h0). Qed.
Lemma lem1200517 {A : Type'} (l : list A) : term35 A l.
Proof. exact (@lem1111732 A l). Qed.
Lemma lem1200518 {A : Type'} (l : list A) : (term35 A l) = ((@List.app A l (@nil A)) = l).
Proof. exact (eq_refl (term35 A l)). Qed.
Lemma lem1200520 {A B : Type'} (b : Prop) : term36 A B b.
Proof. exact (@lem12958 A B b). Qed.
Lemma lem1200521 {A B : Type'} (b : Prop) : (term36 A B b) = (term37 A B b).
Proof. exact (eq_refl (term36 A B b)). Qed.
Lemma lem1200522 {A B : Type'} (b : Prop) : term37 A B b.
Proof. exact (EQ_MP (@lem1200521 A B b) (@lem1200520 A B b)). Qed.
Lemma lem1200523 {A B : Type'} (b : Prop) (f : A -> B) : term38 A B b f.
Proof. exact (@lem1200522 A B b f). Qed.
Lemma lem1200524 {A B : Type'} (b : Prop) (f : A -> B) : (term38 A B b f) = (term39 A B b f).
Proof. exact (eq_refl (term38 A B b f)). Qed.
Lemma lem1200525 {A B : Type'} (b : Prop) (f : A -> B) : term39 A B b f.
Proof. exact (EQ_MP (@lem1200524 A B b f) (@lem1200523 A B b f)). Qed.
Lemma lem1200526 {A B : Type'} (b : Prop) (f : A -> B) (x : A) : term40 A B b f x.
Proof. exact (@lem1200525 A B b f x). Qed.
Lemma lem1200527 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : (term40 A B b f x) = (term41 A B b x f).
Proof. exact (eq_refl (term40 A B b f x)). Qed.
Lemma lem1200528 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : term41 A B b x f.
Proof. exact (EQ_MP (@lem1200527 A B b x f) (@lem1200526 A B b f x)). Qed.
Lemma lem1200529 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : term42 A B b x f y.
Proof. exact (@lem1200528 A B b x f y). Qed.
Lemma lem1200530 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term42 A B b x f y) = ((term43 A B f b x y) = (term44 A B b x f y)).
Proof. exact (eq_refl (term42 A B b x f y)). Qed.
Lemma lem1200555 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term43 A B f b x y) = (term44 A B b x f y).
Proof. exact (EQ_MP (@lem1200530 A B b x f y) (@lem1200529 A B b x f y)). Qed.
Lemma lem1200556 {A : Type'} (b : Prop) (x : list A) (f : type1143 A) (y : list A) : (term45 A f b x y) = (term46 A b x f y).
Proof. exact (@lem1200555 (list A) Prop b x f y). Qed.
Lemma lem1200557 {A : Type'} (l : list A) (m : list A) : ((term47 A l m) = (term48 A l m)) = (term49 A l m).
Proof. exact (@lem1200556 A (m = (@nil A)) (@List.removelast A l) (term50 A l m) (term51 A l m)). Qed.
Lemma lem1200563 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term52 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1200564 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term53 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1200563 _2963 g t e g' t' e'). Qed.
Lemma lem1200565 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term54 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1200564 _2963 g t e g' t'). Qed.
Lemma lem1200566 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term55 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1200565 _2963 g t e g'). Qed.
Lemma lem1200567 (g : Prop) (t : Prop) (e : Prop) : term56 g t e.
Proof. exact (@lem1200566 Prop g t e). Qed.
Lemma lem1200568 {A : Type'} (l : list A) (m : list A) : term57 A l m.
Proof. exact (@lem1200567 (m = (@nil A)) ((term47 A l m) = (@List.removelast A l)) ((term47 A l m) = (term51 A l m))). Qed.
Lemma lem1200569 {A : Type'} (l : list A) (m : list A) (g' : Prop) : term58 A l m g'.
Proof. exact (@lem1200568 A l m g'). Qed.
Lemma lem1200570 {A : Type'} (l : list A) (m : list A) (g' : Prop) : (term58 A l m g') = (term59 A l m g').
Proof. exact (eq_refl (term58 A l m g')). Qed.
Lemma lem1200571 {A : Type'} (l : list A) (m : list A) (g' : Prop) : term59 A l m g'.
Proof. exact (EQ_MP (@lem1200570 A l m g') (@lem1200569 A l m g')). Qed.
Lemma lem1200572 {A : Type'} (l : list A) (m : list A) (g' : Prop) (t' : Prop) : term60 A l m g' t'.
Proof. exact (@lem1200571 A l m g' t'). Qed.
Lemma lem1200573 {A : Type'} (l : list A) (m : list A) (g' : Prop) (t' : Prop) : (term60 A l m g' t') = (term61 A l m g' t').
Proof. exact (eq_refl (term60 A l m g' t')). Qed.
Lemma lem1200574 {A : Type'} (l : list A) (m : list A) (g' : Prop) (t' : Prop) : term61 A l m g' t'.
Proof. exact (EQ_MP (@lem1200573 A l m g' t') (@lem1200572 A l m g' t')). Qed.
Lemma lem1200575 {A : Type'} (l : list A) (m : list A) (g' : Prop) (t' : Prop) (e' : Prop) : term62 A l m g' t' e'.
Proof. exact (@lem1200574 A l m g' t' e'). Qed.
Lemma lem1200576 {A : Type'} (l : list A) (m : list A) (g' : Prop) (t' : Prop) (e' : Prop) : (term62 A l m g' t' e') = (term63 A l m g' t' e').
Proof. exact (eq_refl (term62 A l m g' t' e')). Qed.
Lemma lem1200577 {A : Type'} (l : list A) (m : list A) (g' : Prop) (t' : Prop) (e' : Prop) : term63 A l m g' t' e'.
Proof. exact (EQ_MP (@lem1200576 A l m g' t' e') (@lem1200575 A l m g' t' e')). Qed.
Lemma lem1200590 {A : Type'} (m : list A) : (m = (@nil A)) = (m = (@nil A)).
Proof. exact (eq_refl (m = (@nil A))). Qed.
Lemma lem1200591 {A : Type'} (l : list A) (m : list A) (t' : Prop) (e' : Prop) : term64 A l m t' e'.
Proof. exact (@lem1200577 A l m (m = (@nil A)) t' e'). Qed.
Lemma lem1200592 {A : Type'} (l : list A) (m : list A) (t' : Prop) (e' : Prop) : term65 A l m t' e'.
Proof. exact (@lem1200591 A l m t' e' (@lem1200590 A m)). Qed.
Lemma lem1200615 {A : Type'} (m : list A) (h1 : m = (@nil A)) : m = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1200618 {A : Type'} (l : list A) : (@List.app A l) = (@List.app A l).
Proof. exact (eq_refl (@List.app A l)). Qed.
Lemma lem1200619 {A : Type'} (l : list A) (m : list A) (h1 : m = (@nil A)) : (@List.app A l m) = (@List.app A l (@nil A)).
Proof. exact (MK_COMB (@lem1200618 A l) (@lem1200615 A m h1)). Qed.
Lemma lem1200621 {A : Type'} (l : list A) : (@List.app A l (@nil A)) = l.
Proof. exact (EQ_MP (@lem1200518 A l) (@lem1200517 A l)). Qed.
Lemma lem1200622 {A : Type'} (l : list A) : (@List.app A l (@nil A)) = l.
Proof. exact (@lem1200621 A l). Qed.
Lemma lem1200625 {A : Type'} (l : list A) (m : list A) (h1 : m = (@nil A)) : (@List.app A l m) = l.
Proof. exact (TRANS (@lem1200619 A l m h1) (@lem1200622 A l)). Qed.
Lemma lem1200626 {A : Type'} : (@List.removelast A) = (@List.removelast A).
Proof. exact (eq_refl (@List.removelast A)). Qed.
Lemma lem1200627 {A : Type'} (l : list A) (m : list A) (h1 : m = (@nil A)) : (term47 A l m) = (@List.removelast A l).
Proof. exact (MK_COMB (@lem1200626 A) (@lem1200625 A l m h1)). Qed.
Lemma lem1200634 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1200635 {A : Type'} (l : list A) (m : list A) (h1 : m = (@nil A)) : (term50 A l m) = (term66 A l).
Proof. exact (MK_COMB (@lem1200634 A) (@lem1200627 A l m h1)). Qed.
Lemma lem1200652 {A : Type'} (l : list A) : (@List.removelast A l) = (@List.removelast A l).
Proof. exact (eq_refl (@List.removelast A l)). Qed.
Lemma lem1200653 {A : Type'} (l : list A) (m : list A) (h1 : m = (@nil A)) : ((term47 A l m) = (@List.removelast A l)) = ((@List.removelast A l) = (@List.removelast A l)).
Proof. exact (MK_COMB (@lem1200635 A l m h1) (@lem1200652 A l)). Qed.
Lemma lem1200655 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200656 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1200655 (list A) x). Qed.
Lemma lem1200657 {A : Type'} (l : list A) : ((@List.removelast A l) = (@List.removelast A l)) = True.
Proof. exact (@lem1200656 A (@List.removelast A l)). Qed.
Lemma lem1200660 {A : Type'} (l : list A) (m : list A) (h1 : m = (@nil A)) : ((term47 A l m) = (@List.removelast A l)) = True.
Proof. exact (TRANS (@lem1200653 A l m h1) (@lem1200657 A l)). Qed.
Lemma lem1200661 {A : Type'} (m : list A) (l : list A) : term67 A m l.
Proof. exact (fun h0 : m = (@nil A) => @lem1200660 A l m h0). Qed.
Lemma lem1200662 {A : Type'} (l : list A) (m : list A) (e' : Prop) : term68 A l m e'.
Proof. exact (@lem1200592 A l m True e'). Qed.
Lemma lem1200663 {A : Type'} (l : list A) (m : list A) (e' : Prop) : term69 A l m e'.
Proof. exact (@lem1200662 A l m e' (@lem1200661 A m l)). Qed.
Lemma lem1200714 {A : Type'} (l : list A) (m : list A) : ((term47 A l m) = (term51 A l m)) = ((term47 A l m) = (term51 A l m)).
Proof. exact (eq_refl ((term47 A l m) = (term51 A l m))). Qed.
Lemma lem1200715 {A : Type'} (l : list A) (m : list A) : term70 A l m.
Proof. exact (fun h0 : term71 A m => @lem1200714 A l m). Qed.
Lemma lem1200716 {A : Type'} (l : list A) (m : list A) : term72 A l m.
Proof. exact (@lem1200663 A l m ((term47 A l m) = (term51 A l m))). Qed.
Lemma lem1200717 {A : Type'} (l : list A) (m : list A) : (term49 A l m) = (term73 A l m).
Proof. exact (@lem1200716 A l m (@lem1200715 A l m)). Qed.
Lemma lem1200721 (p : Prop) (q : Prop) : (@COND Prop p True q) = (term1 p q).
Proof. exact (EQ_MP (@lem1200335 p q) (@lem1200515 p q)). Qed.
Lemma lem1200722 {A : Type'} (l : list A) (m : list A) : (term73 A l m) = (term74 A l m).
Proof. exact (@lem1200721 (m = (@nil A)) ((term47 A l m) = (term51 A l m))). Qed.
Lemma lem1200867 {A : Type'} (l : list A) (m : list A) : (term49 A l m) = (term74 A l m).
Proof. exact (TRANS (@lem1200717 A l m) (@lem1200722 A l m)). Qed.
Lemma lem1200868 {A : Type'} (l : list A) (m : list A) : ((term47 A l m) = (term48 A l m)) = (term74 A l m).
Proof. exact (TRANS (@lem1200557 A l m) (@lem1200867 A l m)). Qed.
Lemma lem1200869 {A : Type'} (l : list A) : (term75 A l) = (term76 A l).
Proof. exact (fun_ext (fun m : list A => @lem1200868 A l m)). Qed.
Lemma lem1201016 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1201017 {A : Type'} (l : list A) : (term77 A l) = (term78 A l).
Proof. exact (MK_COMB (@lem1201016 A) (@lem1200869 A l)). Qed.
Lemma lem1201172 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (fun_ext (fun l : list A => @lem1201017 A l)). Qed.
Lemma lem1201329 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1201330 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem1201329 A) (@lem1201172 A)). Qed.
Lemma lem1201495 {A : Type'} : (term82 A) = (term81 A).
Proof. exact (SYM (@lem1201330 A)). Qed.
Lemma lem1201497 {A : Type'} (P : type1143 A) : term83 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1201498 {A : Type'} (P : type1143 A) : term83 A P.
Proof. exact (@lem1201497 A P). Qed.
Lemma lem1201499 {A : Type'} : term84 A.
Proof. exact (@lem1201498 A (term80 A)). Qed.
Lemma lem1201500 {A : Type'} : (term85 A) = (term86 A).
Proof. exact (eq_refl (term85 A)). Qed.
Lemma lem1201501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1201502 {A : Type'} : (term87 A) = (term88 A).
Proof. exact (MK_COMB (@lem1201501) (@lem1201500 A)). Qed.
Lemma lem1201503 {A : Type'} (t : list A) : (term89 A t) = (term78 A t).
Proof. exact (eq_refl (term89 A t)). Qed.
Lemma lem1201504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1201505 {A : Type'} (t : list A) : (term90 A t) = (term91 A t).
Proof. exact (MK_COMB (@lem1201504) (@lem1201503 A t)). Qed.
Lemma lem1201506 {A : Type'} (h : A) (t : list A) : (term92 A h t) = (term93 A h t).
Proof. exact (eq_refl (term92 A h t)). Qed.
Lemma lem1201507 {A : Type'} (h : A) (t : list A) : (term94 A h t) = (term95 A h t).
Proof. exact (MK_COMB (@lem1201505 A t) (@lem1201506 A h t)). Qed.
Lemma lem1201508 {A : Type'} (h : A) : (term96 A h) = (term97 A h).
Proof. exact (fun_ext (fun t : list A => @lem1201507 A h t)). Qed.
Lemma lem1201509 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1201510 {A : Type'} (h : A) : (term98 A h) = (term99 A h).
Proof. exact (MK_COMB (@lem1201509 A) (@lem1201508 A h)). Qed.
Lemma lem1201511 {A : Type'} : (term100 A) = (term101 A).
Proof. exact (fun_ext (fun h : A => @lem1201510 A h)). Qed.
Lemma lem1201512 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1201513 {A : Type'} : (term102 A) = (term103 A).
Proof. exact (MK_COMB (@lem1201512 A) (@lem1201511 A)). Qed.
Lemma lem1201514 {A : Type'} : (term104 A) = (term105 A).
Proof. exact (MK_COMB (@lem1201502 A) (@lem1201513 A)). Qed.
Lemma lem1201515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1201516 {A : Type'} : (term106 A) = (term107 A).
Proof. exact (MK_COMB (@lem1201515) (@lem1201514 A)). Qed.
Lemma lem1201517 {A : Type'} (l : list A) : (term89 A l) = (term78 A l).
Proof. exact (eq_refl (term89 A l)). Qed.
Lemma lem1201518 {A : Type'} : (term108 A) = (term80 A).
Proof. exact (fun_ext (fun l : list A => @lem1201517 A l)). Qed.
Lemma lem1201519 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1201520 {A : Type'} : (term109 A) = (term82 A).
Proof. exact (MK_COMB (@lem1201519 A) (@lem1201518 A)). Qed.
Lemma lem1201521 {A : Type'} : (term84 A) = (term110 A).
Proof. exact (MK_COMB (@lem1201516 A) (@lem1201520 A)). Qed.
Lemma lem1201522 {A : Type'} : term110 A.
Proof. exact (EQ_MP (@lem1201521 A) (@lem1201499 A)). Qed.
Lemma lem1201523 {A : Type'} (t : list A) (h1 : term78 A t) : term78 A t.
Proof. exact (h1). Qed.
Lemma lem1201542 {A : Type'} : term111 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1201543 {A : Type'} (l : list A) : term112 A l.
Proof. exact (@lem1201542 A l). Qed.
Lemma lem1201544 {A : Type'} (l : list A) : (term112 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term112 A l)). Qed.
Lemma lem1201553 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term113 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1201554 (p : Prop) (q : Prop) (p' : Prop) : term114 p q p'.
Proof. exact (fun q' : Prop => @lem1201553 p q p' q'). Qed.
Lemma lem1201555 (p : Prop) (q : Prop) : term115 p q.
Proof. exact (fun p' : Prop => @lem1201554 p q p'). Qed.
Lemma lem1201556 {A : Type'} (m : list A) : term116 A m.
Proof. exact (@lem1201555 (term71 A m) ((term117 A m) = (term118 A m))). Qed.
Lemma lem1201557 {A : Type'} (m : list A) (p' : Prop) : term119 A m p'.
Proof. exact (@lem1201556 A m p'). Qed.
Lemma lem1201558 {A : Type'} (m : list A) (p' : Prop) : (term119 A m p') = (term120 A m p').
Proof. exact (eq_refl (term119 A m p')). Qed.
Lemma lem1201559 {A : Type'} (m : list A) (p' : Prop) : term120 A m p'.
Proof. exact (EQ_MP (@lem1201558 A m p') (@lem1201557 A m p')). Qed.
Lemma lem1201560 {A : Type'} (m : list A) (p' : Prop) (q' : Prop) : term121 A m p' q'.
Proof. exact (@lem1201559 A m p' q'). Qed.
Lemma lem1201561 {A : Type'} (m : list A) (p' : Prop) (q' : Prop) : (term121 A m p' q') = (term122 A m p' q').
Proof. exact (eq_refl (term121 A m p' q')). Qed.
Lemma lem1201562 {A : Type'} (m : list A) (p' : Prop) (q' : Prop) : term122 A m p' q'.
Proof. exact (EQ_MP (@lem1201561 A m p' q') (@lem1201560 A m p' q')). Qed.
Lemma lem1201565 {A : Type'} (m : list A) : (term71 A m) = (term71 A m).
Proof. exact (eq_refl (term71 A m)). Qed.
Lemma lem1201566 {A : Type'} (m : list A) (q' : Prop) : term123 A m q'.
Proof. exact (@lem1201562 A m (term71 A m) q'). Qed.
Lemma lem1201567 {A : Type'} (m : list A) (q' : Prop) : term124 A m q'.
Proof. exact (@lem1201566 A m q' (@lem1201565 A m)). Qed.
Lemma lem1201585 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1201544 A l) (@lem1201543 A l)). Qed.
Lemma lem1201586 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1201585 A l). Qed.
Lemma lem1201587 {A : Type'} (m : list A) : (@List.app A (@nil A) m) = m.
Proof. exact (@lem1201586 A m). Qed.
Lemma lem1201588 {A : Type'} : (@List.removelast A) = (@List.removelast A).
Proof. exact (eq_refl (@List.removelast A)). Qed.
Lemma lem1201589 {A : Type'} (m : list A) : (term117 A m) = (@List.removelast A m).
Proof. exact (MK_COMB (@lem1201588 A) (@lem1201587 A m)). Qed.
Lemma lem1201590 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1201591 {A : Type'} (m : list A) : (term125 A m) = (term66 A m).
Proof. exact (MK_COMB (@lem1201590 A) (@lem1201589 A m)). Qed.
Lemma lem1201593 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1201544 A l) (@lem1201543 A l)). Qed.
Lemma lem1201594 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1201593 A l). Qed.
Lemma lem1201595 {A : Type'} (m : list A) : (term118 A m) = (@List.removelast A m).
Proof. exact (@lem1201594 A (@List.removelast A m)). Qed.
Lemma lem1201596 {A : Type'} (m : list A) : ((term117 A m) = (term118 A m)) = ((@List.removelast A m) = (@List.removelast A m)).
Proof. exact (MK_COMB (@lem1201591 A m) (@lem1201595 A m)). Qed.
Lemma lem1201598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1201599 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1201598 (list A) x). Qed.
Lemma lem1201600 {A : Type'} (m : list A) : ((@List.removelast A m) = (@List.removelast A m)) = True.
Proof. exact (@lem1201599 A (@List.removelast A m)). Qed.
Lemma lem1201601 {A : Type'} (m : list A) : ((term117 A m) = (term118 A m)) = True.
Proof. exact (TRANS (@lem1201596 A m) (@lem1201600 A m)). Qed.
Lemma lem1201602 {A : Type'} (m : list A) : term126 A m.
Proof. exact (fun h0 : term71 A m => @lem1201601 A m). Qed.
Lemma lem1201603 {A : Type'} (m : list A) : term127 A m.
Proof. exact (@lem1201567 A m True). Qed.
Lemma lem1201604 {A : Type'} (m : list A) : (term128 A m) = (term129 A m).
Proof. exact (@lem1201603 A m (@lem1201602 A m)). Qed.
Lemma lem1201606 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1201607 {A : Type'} (m : list A) : (term129 A m) = True.
Proof. exact (@lem1201606 (term71 A m)). Qed.
Lemma lem1201608 {A : Type'} (m : list A) : (term128 A m) = True.
Proof. exact (TRANS (@lem1201604 A m) (@lem1201607 A m)). Qed.
Lemma lem1201609 {A : Type'} : (term130 A) = (term131 A).
Proof. exact (fun_ext (fun m : list A => @lem1201608 A m)). Qed.
Lemma lem1201610 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1201611 {A : Type'} : (term86 A) = (term132 A).
Proof. exact (MK_COMB (@lem1201610 A) (@lem1201609 A)). Qed.
Lemma lem1201613 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1201614 {A : Type'} (t : Prop) : (term133 A t) = t.
Proof. exact (@lem1201613 (list A) t). Qed.
Lemma lem1201615 {A : Type'} : (term132 A) = True.
Proof. exact (@lem1201614 A True). Qed.
Lemma lem1201616 {A : Type'} : (term86 A) = True.
Proof. exact (TRANS (@lem1201611 A) (@lem1201615 A)). Qed.
Lemma lem1201617 {A : Type'} : True = (term86 A).
Proof. exact (SYM (@lem1201616 A)). Qed.
Lemma lem1201618 {A : Type'} : term86 A.
Proof. exact (EQ_MP (@lem1201617 A) (@lem0)). Qed.
Lemma lem1201619 {_27653 : Type'} (l : list _27653) : term134 _27653 l.
Proof. exact (@lem1187397 _27653 l). Qed.
Lemma lem1201620 {_27653 : Type'} (l : list _27653) : (term134 _27653 l) = (term135 _27653 l).
Proof. exact (eq_refl (term134 _27653 l)). Qed.
Lemma lem1201621 {_27653 : Type'} (l : list _27653) : term135 _27653 l.
Proof. exact (EQ_MP (@lem1201620 _27653 l) (@lem1201619 _27653 l)). Qed.
Lemma lem1201622 {_27653 : Type'} (l : list _27653) (m : list _27653) : term136 _27653 l m.
Proof. exact (@lem1201621 _27653 l m). Qed.
Lemma lem1201623 {_27653 : Type'} (l : list _27653) (m : list _27653) : (term136 _27653 l m) = (((@List.app _27653 l m) = (@nil _27653)) = (term137 _27653 l m)).
Proof. exact (eq_refl (term136 _27653 l m)). Qed.
Lemma lem1201627 {A : Type'} : term138 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1201628 {A : Type'} (h : A) : term139 A h.
Proof. exact (@lem1201627 A h). Qed.
Lemma lem1201629 {A : Type'} (h : A) : (term139 A h) = (term140 A h).
Proof. exact (eq_refl (term139 A h)). Qed.
Lemma lem1201630 {A : Type'} (h : A) : term140 A h.
Proof. exact (EQ_MP (@lem1201629 A h) (@lem1201628 A h)). Qed.
Lemma lem1201631 {A : Type'} (h : A) (t : list A) : term141 A h t.
Proof. exact (@lem1201630 A h t). Qed.
Lemma lem1201632 {A : Type'} (h : A) (t : list A) : (term141 A h t) = (term142 A h t).
Proof. exact (eq_refl (term141 A h t)). Qed.
Lemma lem1201633 {A : Type'} (h : A) (t : list A) : term142 A h t.
Proof. exact (EQ_MP (@lem1201632 A h t) (@lem1201631 A h t)). Qed.
Lemma lem1201634 {A : Type'} (h : A) (t : list A) (l : list A) : term143 A h t l.
Proof. exact (@lem1201633 A h t l). Qed.
Lemma lem1201635 {A : Type'} (h : A) (t : list A) (l : list A) : (term143 A h t l) = ((term144 A h t l) = (term145 A h t l)).
Proof. exact (eq_refl (term143 A h t l)). Qed.
Lemma lem1201641 {A : Type'} (m : list A) (t : list A) (h1 : term78 A t) : term146 A t m.
Proof. exact (@lem1201523 A t h1 m). Qed.
Lemma lem1201642 {A : Type'} (t : list A) (m : list A) : (term146 A t m) = (term74 A t m).
Proof. exact (eq_refl (term146 A t m)). Qed.
Lemma lem1201643 {A : Type'} (m : list A) (t : list A) (h1 : term78 A t) : term74 A t m.
Proof. exact (EQ_MP (@lem1201642 A t m) (@lem1201641 A m t h1)). Qed.
Lemma lem1201644 {A : Type'} (m : list A) (h1 : term71 A m) : term71 A m.
Proof. exact (h1). Qed.
Lemma lem1201645 {A : Type'} (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term47 A t m) = (term51 A t m).
Proof. exact (@lem1201643 A m t h1 (@lem1201644 A m h2)). Qed.
Lemma lem1201658 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term113 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1201659 (p : Prop) (q : Prop) (p' : Prop) : term114 p q p'.
Proof. exact (fun q' : Prop => @lem1201658 p q p' q'). Qed.
Lemma lem1201660 (p : Prop) (q : Prop) : term115 p q.
Proof. exact (fun p' : Prop => @lem1201659 p q p'). Qed.
Lemma lem1201661 {A : Type'} (h : A) (t : list A) (m : list A) : term147 A h t m.
Proof. exact (@lem1201660 (term71 A m) ((term148 A h t m) = (term149 A h t m))). Qed.
Lemma lem1201662 {A : Type'} (h : A) (t : list A) (m : list A) (p' : Prop) : term150 A h t m p'.
Proof. exact (@lem1201661 A h t m p'). Qed.
Lemma lem1201663 {A : Type'} (h : A) (t : list A) (m : list A) (p' : Prop) : (term150 A h t m p') = (term151 A h t m p').
Proof. exact (eq_refl (term150 A h t m p')). Qed.
Lemma lem1201664 {A : Type'} (h : A) (t : list A) (m : list A) (p' : Prop) : term151 A h t m p'.
Proof. exact (EQ_MP (@lem1201663 A h t m p') (@lem1201662 A h t m p')). Qed.
Lemma lem1201665 {A : Type'} (h : A) (t : list A) (m : list A) (p' : Prop) (q' : Prop) : term152 A h t m p' q'.
Proof. exact (@lem1201664 A h t m p' q'). Qed.
Lemma lem1201666 {A : Type'} (h : A) (t : list A) (m : list A) (p' : Prop) (q' : Prop) : (term152 A h t m p' q') = (term153 A h t m p' q').
Proof. exact (eq_refl (term152 A h t m p' q')). Qed.
Lemma lem1201667 {A : Type'} (h : A) (t : list A) (m : list A) (p' : Prop) (q' : Prop) : term153 A h t m p' q'.
Proof. exact (EQ_MP (@lem1201666 A h t m p' q') (@lem1201665 A h t m p' q')). Qed.
Lemma lem1201670 {A : Type'} (m : list A) : (term71 A m) = (term71 A m).
Proof. exact (eq_refl (term71 A m)). Qed.
Lemma lem1201671 {A : Type'} (h : A) (t : list A) (m : list A) (q' : Prop) : term154 A h t m q'.
Proof. exact (@lem1201667 A h t m (term71 A m) q'). Qed.
Lemma lem1201672 {A : Type'} (h : A) (t : list A) (m : list A) (q' : Prop) : term155 A h t m q'.
Proof. exact (@lem1201671 A h t m q' (@lem1201670 A m)). Qed.
Lemma lem1201673 {A : Type'} (m : list A) (h1 : term71 A m) : term71 A m.
Proof. exact (h1). Qed.
Lemma lem1201674 {A : Type'} (m : list A) : term156 A m.
Proof. exact (@lem82 (m = (@nil A))). Qed.
Lemma lem1201690 {A : Type'} (h : A) (t : list A) (l : list A) : (term144 A h t l) = (term145 A h t l).
Proof. exact (EQ_MP (@lem1201635 A h t l) (@lem1201634 A h t l)). Qed.
Lemma lem1201691 {A : Type'} (h : A) (t : list A) (l : list A) : (term144 A h t l) = (term145 A h t l).
Proof. exact (@lem1201690 A h t l). Qed.
Lemma lem1201692 {A : Type'} (h : A) (t : list A) (m : list A) : (term144 A h t m) = (term145 A h t m).
Proof. exact (@lem1201691 A h t m). Qed.
Lemma lem1201693 {A : Type'} : (@List.removelast A) = (@List.removelast A).
Proof. exact (eq_refl (@List.removelast A)). Qed.
Lemma lem1201694 {A : Type'} (h : A) (t : list A) (m : list A) : (term148 A h t m) = (term157 A h t m).
Proof. exact (MK_COMB (@lem1201693 A) (@lem1201692 A h t m)). Qed.
Lemma lem1201696 {_25251 : Type'} (h : _25251) (t : list _25251) : (term158 _25251 h t) = (term159 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1201697 {A : Type'} (h : A) (t : list A) : (term158 A h t) = (term159 A h t).
Proof. exact (@lem1201696 A h t). Qed.
Lemma lem1201698 {A : Type'} (h : A) (t : list A) (m : list A) : (term157 A h t m) = (term160 A h t m).
Proof. exact (@lem1201697 A h (@List.app A t m)). Qed.
Lemma lem1201702 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term52 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1201703 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term53 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1201702 _2963 g t e g' t' e'). Qed.
Lemma lem1201704 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term54 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1201703 _2963 g t e g' t'). Qed.
Lemma lem1201705 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term55 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1201704 _2963 g t e g'). Qed.
Lemma lem1201706 {A : Type'} (g : Prop) (t : list A) (e : list A) : term161 A g t e.
Proof. exact (@lem1201705 (list A) g t e). Qed.
Lemma lem1201707 {A : Type'} (h : A) (t : list A) (m : list A) : term162 A h t m.
Proof. exact (@lem1201706 A ((@List.app A t m) = (@nil A)) (@nil A) (term163 A h t m)). Qed.
Lemma lem1201708 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) : term164 A h t m g'.
Proof. exact (@lem1201707 A h t m g'). Qed.
Lemma lem1201709 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) : (term164 A h t m g') = (term165 A h t m g').
Proof. exact (eq_refl (term164 A h t m g')). Qed.
Lemma lem1201710 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) : term165 A h t m g'.
Proof. exact (EQ_MP (@lem1201709 A h t m g') (@lem1201708 A h t m g')). Qed.
Lemma lem1201711 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) (t' : list A) : term166 A h t m g' t'.
Proof. exact (@lem1201710 A h t m g' t'). Qed.
Lemma lem1201712 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) (t' : list A) : (term166 A h t m g' t') = (term167 A h t m g' t').
Proof. exact (eq_refl (term166 A h t m g' t')). Qed.
Lemma lem1201713 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) (t' : list A) : term167 A h t m g' t'.
Proof. exact (EQ_MP (@lem1201712 A h t m g' t') (@lem1201711 A h t m g' t')). Qed.
Lemma lem1201714 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) (t' : list A) (e' : list A) : term168 A h t m g' t' e'.
Proof. exact (@lem1201713 A h t m g' t' e'). Qed.
Lemma lem1201715 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) (t' : list A) (e' : list A) : (term168 A h t m g' t' e') = (term169 A h t m g' t' e').
Proof. exact (eq_refl (term168 A h t m g' t' e')). Qed.
Lemma lem1201716 {A : Type'} (h : A) (t : list A) (m : list A) (g' : Prop) (t' : list A) (e' : list A) : term169 A h t m g' t' e'.
Proof. exact (EQ_MP (@lem1201715 A h t m g' t' e') (@lem1201714 A h t m g' t' e')). Qed.
Lemma lem1201718 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((@List.app _27653 l m) = (@nil _27653)) = (term137 _27653 l m).
Proof. exact (EQ_MP (@lem1201623 _27653 l m) (@lem1201622 _27653 l m)). Qed.
Lemma lem1201719 {A : Type'} (l : list A) (m : list A) : ((@List.app A l m) = (@nil A)) = (term137 A l m).
Proof. exact (@lem1201718 A l m). Qed.
Lemma lem1201720 {A : Type'} (t : list A) (m : list A) : ((@List.app A t m) = (@nil A)) = (term137 A t m).
Proof. exact (@lem1201719 A t m). Qed.
Lemma lem1201726 {A : Type'} (m : list A) (h1 : term71 A m) : (m = (@nil A)) = False.
Proof. exact (@lem1201674 A m (@lem1201673 A m h1)). Qed.
Lemma lem1201727 {A : Type'} (t : list A) : (term170 A t) = (term170 A t).
Proof. exact (eq_refl (term170 A t)). Qed.
Lemma lem1201728 {A : Type'} (t : list A) (m : list A) (h1 : term71 A m) : (term137 A t m) = (term171 A t).
Proof. exact (MK_COMB (@lem1201727 A t) (@lem1201726 A m h1)). Qed.
Lemma lem1201730 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1201731 {A : Type'} (t : list A) : (term171 A t) = False.
Proof. exact (@lem1201730 (t = (@nil A))). Qed.
Lemma lem1201732 {A : Type'} (t : list A) (m : list A) (h1 : term71 A m) : (term137 A t m) = False.
Proof. exact (TRANS (@lem1201728 A t m h1) (@lem1201731 A t)). Qed.
Lemma lem1201733 {A : Type'} (t : list A) (m : list A) (h1 : term71 A m) : ((@List.app A t m) = (@nil A)) = False.
Proof. exact (TRANS (@lem1201720 A t m) (@lem1201732 A t m h1)). Qed.
Lemma lem1201734 {A : Type'} (h : A) (t : list A) (m : list A) (t' : list A) (e' : list A) : term172 A h t m t' e'.
Proof. exact (@lem1201716 A h t m False t' e'). Qed.
Lemma lem1201735 {A : Type'} (h : A) (t : list A) (t' : list A) (e' : list A) (m : list A) (h1 : term71 A m) : term173 A h t m t' e'.
Proof. exact (@lem1201734 A h t m t' e' (@lem1201733 A t m h1)). Qed.
Lemma lem1201739 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1201740 {A : Type'} : term174 A.
Proof. exact (fun h0 : False => @lem1201739 A). Qed.
Lemma lem1201741 {A : Type'} (h : A) (t : list A) (e' : list A) (m : list A) (h1 : term71 A m) : term175 A h t m e'.
Proof. exact (@lem1201735 A h t (@nil A) e' m h1). Qed.
Lemma lem1201742 {A : Type'} (h : A) (t : list A) (e' : list A) (m : list A) (h1 : term71 A m) : term176 A h t m e'.
Proof. exact (@lem1201741 A h t e' m h1 (@lem1201740 A)). Qed.
Lemma lem1201749 {A : Type'} (m : list A) (t : list A) (h1 : term78 A t) : term74 A t m.
Proof. exact (fun h0 : term71 A m => @lem1201645 A t m h1 h0). Qed.
Lemma lem1201750 {A : Type'} (m : list A) (t : list A) (h1 : term78 A t) : term74 A t m.
Proof. exact (@lem1201749 A m t h1). Qed.
Lemma lem1201752 {A : Type'} (m : list A) (h1 : term71 A m) : (m = (@nil A)) = False.
Proof. exact (@lem1201674 A m (@lem1201673 A m h1)). Qed.
Lemma lem1201755 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1201756 {A : Type'} (m : list A) (h1 : term71 A m) : (term71 A m) = (~ False).
Proof. exact (MK_COMB (@lem1201755) (@lem1201752 A m h1)). Qed.
Lemma lem1201758 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1201759 {A : Type'} (m : list A) (h1 : term71 A m) : (term71 A m) = True.
Proof. exact (TRANS (@lem1201756 A m h1) (@lem1201758)). Qed.
Lemma lem1201760 {A : Type'} (m : list A) (h1 : term71 A m) : True = (term71 A m).
Proof. exact (SYM (@lem1201759 A m h1)). Qed.
Lemma lem1201761 {A : Type'} (m : list A) (h1 : term71 A m) : term71 A m.
Proof. exact (EQ_MP (@lem1201760 A m h1) (@lem0)). Qed.
Lemma lem1201762 {A : Type'} (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term47 A t m) = (term51 A t m).
Proof. exact (@lem1201750 A m t h1 (@lem1201761 A m h2)). Qed.
Lemma lem1201763 {A : Type'} (h : A) : (@cons A h) = (@cons A h).
Proof. exact (eq_refl (@cons A h)). Qed.
Lemma lem1201764 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term163 A h t m) = (term177 A h t m).
Proof. exact (MK_COMB (@lem1201763 A h) (@lem1201762 A t m h1 h2)). Qed.
Lemma lem1201765 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : term178 A h t m.
Proof. exact (fun h0 : ~ False => @lem1201764 A h t m h1 h2). Qed.
Lemma lem1201766 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term71 A m) : term179 A h t m.
Proof. exact (@lem1201742 A h t (term177 A h t m) m h1). Qed.
Lemma lem1201767 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term160 A h t m) = (term180 A h t m).
Proof. exact (@lem1201766 A h t m h2 (@lem1201765 A h t m h1 h2)). Qed.
Lemma lem1201769 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1201770 {A : Type'} (t1 : list A) (t2 : list A) : (@COND (list A) False t1 t2) = t2.
Proof. exact (@lem1201769 (list A) t1 t2). Qed.
Lemma lem1201771 {A : Type'} (h : A) (t : list A) (m : list A) : (term180 A h t m) = (term177 A h t m).
Proof. exact (@lem1201770 A (@nil A) (term177 A h t m)). Qed.
Lemma lem1201772 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term160 A h t m) = (term177 A h t m).
Proof. exact (TRANS (@lem1201767 A h t m h1 h2) (@lem1201771 A h t m)). Qed.
Lemma lem1201773 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term157 A h t m) = (term177 A h t m).
Proof. exact (TRANS (@lem1201698 A h t m) (@lem1201772 A h t m h1 h2)). Qed.
Lemma lem1201774 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term148 A h t m) = (term177 A h t m).
Proof. exact (TRANS (@lem1201694 A h t m) (@lem1201773 A h t m h1 h2)). Qed.
Lemma lem1201775 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1201776 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : (term181 A h t m) = (term182 A h t m).
Proof. exact (MK_COMB (@lem1201775 A) (@lem1201774 A h t m h1 h2)). Qed.
Lemma lem1201778 {A : Type'} (h : A) (t : list A) (l : list A) : (term144 A h t l) = (term145 A h t l).
Proof. exact (EQ_MP (@lem1201635 A h t l) (@lem1201634 A h t l)). Qed.
Lemma lem1201779 {A : Type'} (h : A) (t : list A) (l : list A) : (term144 A h t l) = (term145 A h t l).
Proof. exact (@lem1201778 A h t l). Qed.
Lemma lem1201780 {A : Type'} (h : A) (t : list A) (m : list A) : (term149 A h t m) = (term177 A h t m).
Proof. exact (@lem1201779 A h t (@List.removelast A m)). Qed.
Lemma lem1201781 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : ((term148 A h t m) = (term149 A h t m)) = ((term177 A h t m) = (term177 A h t m)).
Proof. exact (MK_COMB (@lem1201776 A h t m h1 h2) (@lem1201780 A h t m)). Qed.
Lemma lem1201783 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1201784 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1201783 (list A) x). Qed.
Lemma lem1201785 {A : Type'} (h : A) (t : list A) (m : list A) : ((term177 A h t m) = (term177 A h t m)) = True.
Proof. exact (@lem1201784 A (term177 A h t m)). Qed.
Lemma lem1201786 {A : Type'} (h : A) (t : list A) (m : list A) (h1 : term78 A t) (h2 : term71 A m) : ((term148 A h t m) = (term149 A h t m)) = True.
Proof. exact (TRANS (@lem1201781 A h t m h1 h2) (@lem1201785 A h t m)). Qed.
Lemma lem1201787 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term78 A t) : term183 A h t m.
Proof. exact (fun h0 : term71 A m => @lem1201786 A h t m h1 h0). Qed.
Lemma lem1201788 {A : Type'} (h : A) (t : list A) (m : list A) : term184 A h t m.
Proof. exact (@lem1201672 A h t m True). Qed.
Lemma lem1201789 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term78 A t) : (term185 A h t m) = (term129 A m).
Proof. exact (@lem1201788 A h t m (@lem1201787 A h m t h1)). Qed.
Lemma lem1201791 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1201792 {A : Type'} (m : list A) : (term129 A m) = True.
Proof. exact (@lem1201791 (term71 A m)). Qed.
Lemma lem1201793 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term78 A t) : (term185 A h t m) = True.
Proof. exact (TRANS (@lem1201789 A h m t h1) (@lem1201792 A m)). Qed.
Lemma lem1201794 {A : Type'} (h : A) (t : list A) (h1 : term78 A t) : (term186 A h t) = (term131 A).
Proof. exact (fun_ext (fun m : list A => @lem1201793 A h m t h1)). Qed.
Lemma lem1201795 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1201796 {A : Type'} (h : A) (t : list A) (h1 : term78 A t) : (term93 A h t) = (term132 A).
Proof. exact (MK_COMB (@lem1201795 A) (@lem1201794 A h t h1)). Qed.
Lemma lem1201798 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1201799 {A : Type'} (t : Prop) : (term133 A t) = t.
Proof. exact (@lem1201798 (list A) t). Qed.
Lemma lem1201800 {A : Type'} : (term132 A) = True.
Proof. exact (@lem1201799 A True). Qed.
Lemma lem1201801 {A : Type'} (h : A) (t : list A) (h1 : term78 A t) : (term93 A h t) = True.
Proof. exact (TRANS (@lem1201796 A h t h1) (@lem1201800 A)). Qed.
Lemma lem1201802 {A : Type'} (h : A) (t : list A) (h1 : term78 A t) : True = (term93 A h t).
Proof. exact (SYM (@lem1201801 A h t h1)). Qed.
Lemma lem1201803 {A : Type'} (h : A) (t : list A) (h1 : term78 A t) : term93 A h t.
Proof. exact (EQ_MP (@lem1201802 A h t h1) (@lem0)). Qed.
Lemma lem1201804 {A : Type'} (h : A) (t : list A) : term95 A h t.
Proof. exact (fun h0 : term78 A t => @lem1201803 A h t h0). Qed.
Lemma lem1201809 {A : Type'} (h : A) : term99 A h.
Proof. exact (fun t : list A => @lem1201804 A h t). Qed.
Lemma lem1201814 {A : Type'} : term103 A.
Proof. exact (fun h : A => @lem1201809 A h). Qed.
Lemma lem1201815 {A : Type'} : term105 A.
Proof. exact (conj (@lem1201618 A) (@lem1201814 A)). Qed.
Lemma lem1201816 {A : Type'} : term82 A.
Proof. exact (@lem1201522 A (@lem1201815 A)). Qed.
Lemma lem1201817 {A : Type'} : term81 A.
Proof. exact (EQ_MP (@lem1201495 A) (@lem1201816 A)). Qed.
