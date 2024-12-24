Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_DIFF_FINITE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import FINITE_SUBSET_spec.
Require Import FINITE_UNION_spec.
Require Import INFINITE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem3631353 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3631354 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3631353 A h1 s). Qed.
Lemma lem3631355 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3631356 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3631355 A s) (@lem3631354 A s h1)). Qed.
Lemma lem3631357 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3631356 A s h1 t). Qed.
Lemma lem3631358 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3631359 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3631358 A t s) (@lem3631357 A s t h1)). Qed.
Lemma lem3631360 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3631361 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3631359 A t s h1 (@lem3631360 A s t h2)). Qed.
Lemma lem3631362 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3631361 A s t h0 h1). Qed.
Lemma lem3631363 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3631364 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3631363 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3631362 A s t h0)). Qed.
Lemma lem3631365 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3631366 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3631364 A s h2 (@lem3631365 A h1)). Qed.
Lemma lem3631367 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3631366 A s h1 h0). Qed.
Lemma lem3631368 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3631367 A s h1). Qed.
Lemma lem3631369 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3631368 A h0). Qed.
Lemma lem3631370 {A : Type'} : term10 A.
Proof. exact (@lem3631369 A (@lem3599924 A)). Qed.
Lemma lem3631371 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3631370 A s). Qed.
Lemma lem3631372 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3631374 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem3631375 {A : Type'} (s : A -> Prop) : (term13 A s) = ((@INFINITE A s) = (term14 A s)).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem3631389 (b : Prop) : term15 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem3631390 (b : Prop) : (term15 b) = (term16 b).
Proof. exact (eq_refl (term15 b)). Qed.
Lemma lem3631391 (b : Prop) : term16 b.
Proof. exact (EQ_MP (@lem3631390 b) (@lem3631389 b)). Qed.
Lemma lem3631392 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem3631393 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem3631406 (a : Prop) (c : Prop) : (term17 a c) = (term17 a c).
Proof. exact (eq_refl (term17 a c)). Qed.
Lemma lem3631407 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term18 a c b) = (term19 a c).
Proof. exact (MK_COMB (@lem3631406 a c) (@lem3631392 b h1)). Qed.
Lemma lem3631408 (a : Prop) (c : Prop) : (term19 a c) = (term20 a c).
Proof. exact (eq_refl (term19 a c)). Qed.
Lemma lem3631409 (a : Prop) (c : Prop) (b : Prop) : (term21 a c b) = (term21 a c b).
Proof. exact (eq_refl (term21 a c b)). Qed.
Lemma lem3631410 (b : Prop) (a : Prop) (c : Prop) : ((term18 a c b) = (term19 a c)) = ((term18 a c b) = (term20 a c)).
Proof. exact (MK_COMB (@lem3631409 a c b) (@lem3631408 a c)). Qed.
Lemma lem3631411 (a : Prop) (b : Prop) (c : Prop) : (term18 a c b) = (term22 a b c).
Proof. exact (eq_refl (term18 a c b)). Qed.
Lemma lem3631412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3631413 (a : Prop) (b : Prop) (c : Prop) : (term21 a c b) = (term23 a b c).
Proof. exact (MK_COMB (@lem3631412) (@lem3631411 a b c)). Qed.
Lemma lem3631414 (a : Prop) (c : Prop) : (term20 a c) = (term20 a c).
Proof. exact (eq_refl (term20 a c)). Qed.
Lemma lem3631415 (b : Prop) (a : Prop) (c : Prop) : ((term18 a c b) = (term20 a c)) = ((term22 a b c) = (term20 a c)).
Proof. exact (MK_COMB (@lem3631413 a b c) (@lem3631414 a c)). Qed.
Lemma lem3631416 (b : Prop) (a : Prop) (c : Prop) : ((term18 a c b) = (term19 a c)) = ((term22 a b c) = (term20 a c)).
Proof. exact (TRANS (@lem3631410 b a c) (@lem3631415 b a c)). Qed.
Lemma lem3631417 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term22 a b c) = (term20 a c).
Proof. exact (EQ_MP (@lem3631416 b a c) (@lem3631407 a c b h1)). Qed.
Lemma lem3631418 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term20 a c) = (term22 a b c).
Proof. exact (SYM (@lem3631417 a c b h1)). Qed.
Lemma lem3631419 (a : Prop) (c : Prop) : (term17 a c) = (term17 a c).
Proof. exact (eq_refl (term17 a c)). Qed.
Lemma lem3631420 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term18 a c b) = (term24 a c).
Proof. exact (MK_COMB (@lem3631419 a c) (@lem3631393 b h1)). Qed.
Lemma lem3631421 (a : Prop) (c : Prop) : (term24 a c) = (term25 a c).
Proof. exact (eq_refl (term24 a c)). Qed.
Lemma lem3631422 (a : Prop) (c : Prop) (b : Prop) : (term21 a c b) = (term21 a c b).
Proof. exact (eq_refl (term21 a c b)). Qed.
Lemma lem3631423 (b : Prop) (a : Prop) (c : Prop) : ((term18 a c b) = (term24 a c)) = ((term18 a c b) = (term25 a c)).
Proof. exact (MK_COMB (@lem3631422 a c b) (@lem3631421 a c)). Qed.
Lemma lem3631424 (a : Prop) (b : Prop) (c : Prop) : (term18 a c b) = (term22 a b c).
Proof. exact (eq_refl (term18 a c b)). Qed.
Lemma lem3631425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3631426 (a : Prop) (b : Prop) (c : Prop) : (term21 a c b) = (term23 a b c).
Proof. exact (MK_COMB (@lem3631425) (@lem3631424 a b c)). Qed.
Lemma lem3631427 (a : Prop) (c : Prop) : (term25 a c) = (term25 a c).
Proof. exact (eq_refl (term25 a c)). Qed.
Lemma lem3631428 (b : Prop) (a : Prop) (c : Prop) : ((term18 a c b) = (term25 a c)) = ((term22 a b c) = (term25 a c)).
Proof. exact (MK_COMB (@lem3631426 a b c) (@lem3631427 a c)). Qed.
Lemma lem3631429 (b : Prop) (a : Prop) (c : Prop) : ((term18 a c b) = (term24 a c)) = ((term22 a b c) = (term25 a c)).
Proof. exact (TRANS (@lem3631423 b a c) (@lem3631428 b a c)). Qed.
Lemma lem3631430 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term22 a b c) = (term25 a c).
Proof. exact (EQ_MP (@lem3631429 b a c) (@lem3631420 a c b h1)). Qed.
Lemma lem3631431 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term25 a c) = (term22 a b c).
Proof. exact (SYM (@lem3631430 a c b h1)). Qed.
Lemma lem3631437 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3631438 (c : Prop) : (term26 c) = (~ c).
Proof. exact (@lem3631437 (~ c)). Qed.
Lemma lem3631439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631440 (c : Prop) : (term27 c) = (term28 c).
Proof. exact (MK_COMB (@lem3631439) (@lem3631438 c)). Qed.
Lemma lem3631441 (a : Prop) : (~ a) = (~ a).
Proof. exact (eq_refl (~ a)). Qed.
Lemma lem3631442 (c : Prop) (a : Prop) : (term29 c a) = (term30 c a).
Proof. exact (MK_COMB (@lem3631440 c) (@lem3631441 a)). Qed.
Lemma lem3631445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631446 (c : Prop) (a : Prop) : (term31 c a) = (term32 c a).
Proof. exact (MK_COMB (@lem3631445) (@lem3631442 c a)). Qed.
Lemma lem3631450 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3631451 (a : Prop) : (a /\ True) = a.
Proof. exact (@lem3631450 a). Qed.
Lemma lem3631452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631453 (a : Prop) : (term33 a) = (imp a).
Proof. exact (MK_COMB (@lem3631452) (@lem3631451 a)). Qed.
Lemma lem3631454 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3631455 (a : Prop) (c : Prop) : (term34 a c) = (a -> c).
Proof. exact (MK_COMB (@lem3631453 a) (@lem3631454 c)). Qed.
Lemma lem3631458 (a : Prop) (c : Prop) : (term20 a c) = (term35 a c).
Proof. exact (MK_COMB (@lem3631446 c a) (@lem3631455 a c)). Qed.
Lemma lem3631461 (a : Prop) (c : Prop) : (term35 a c) = (term20 a c).
Proof. exact (SYM (@lem3631458 a c)). Qed.
Lemma lem3631462 (c : Prop) : term15 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem3631463 (c : Prop) : (term15 c) = (term16 c).
Proof. exact (eq_refl (term15 c)). Qed.
Lemma lem3631464 (c : Prop) : term16 c.
Proof. exact (EQ_MP (@lem3631463 c) (@lem3631462 c)). Qed.
Lemma lem3631465 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem3631466 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem3631475 (a : Prop) : (term36 a) = (term36 a).
Proof. exact (eq_refl (term36 a)). Qed.
Lemma lem3631476 (a : Prop) (c : Prop) (h1 : c = True) : (term37 a c) = (term38 a).
Proof. exact (MK_COMB (@lem3631475 a) (@lem3631465 c h1)). Qed.
Lemma lem3631477 (a : Prop) : (term38 a) = (term39 a).
Proof. exact (eq_refl (term38 a)). Qed.
Lemma lem3631478 (a : Prop) (c : Prop) : (term40 a c) = (term40 a c).
Proof. exact (eq_refl (term40 a c)). Qed.
Lemma lem3631479 (c : Prop) (a : Prop) : ((term37 a c) = (term38 a)) = ((term37 a c) = (term39 a)).
Proof. exact (MK_COMB (@lem3631478 a c) (@lem3631477 a)). Qed.
Lemma lem3631480 (a : Prop) (c : Prop) : (term37 a c) = (term35 a c).
Proof. exact (eq_refl (term37 a c)). Qed.
Lemma lem3631481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3631482 (a : Prop) (c : Prop) : (term40 a c) = (term41 a c).
Proof. exact (MK_COMB (@lem3631481) (@lem3631480 a c)). Qed.
Lemma lem3631483 (a : Prop) : (term39 a) = (term39 a).
Proof. exact (eq_refl (term39 a)). Qed.
Lemma lem3631484 (c : Prop) (a : Prop) : ((term37 a c) = (term39 a)) = ((term35 a c) = (term39 a)).
Proof. exact (MK_COMB (@lem3631482 a c) (@lem3631483 a)). Qed.
Lemma lem3631485 (c : Prop) (a : Prop) : ((term37 a c) = (term38 a)) = ((term35 a c) = (term39 a)).
Proof. exact (TRANS (@lem3631479 c a) (@lem3631484 c a)). Qed.
Lemma lem3631486 (a : Prop) (c : Prop) (h1 : c = True) : (term35 a c) = (term39 a).
Proof. exact (EQ_MP (@lem3631485 c a) (@lem3631476 a c h1)). Qed.
Lemma lem3631487 (a : Prop) (c : Prop) (h1 : c = True) : (term39 a) = (term35 a c).
Proof. exact (SYM (@lem3631486 a c h1)). Qed.
Lemma lem3631488 (a : Prop) : (term36 a) = (term36 a).
Proof. exact (eq_refl (term36 a)). Qed.
Lemma lem3631489 (a : Prop) (c : Prop) (h1 : c = False) : (term37 a c) = (term42 a).
Proof. exact (MK_COMB (@lem3631488 a) (@lem3631466 c h1)). Qed.
Lemma lem3631490 (a : Prop) : (term42 a) = (term43 a).
Proof. exact (eq_refl (term42 a)). Qed.
Lemma lem3631491 (a : Prop) (c : Prop) : (term40 a c) = (term40 a c).
Proof. exact (eq_refl (term40 a c)). Qed.
Lemma lem3631492 (c : Prop) (a : Prop) : ((term37 a c) = (term42 a)) = ((term37 a c) = (term43 a)).
Proof. exact (MK_COMB (@lem3631491 a c) (@lem3631490 a)). Qed.
Lemma lem3631493 (a : Prop) (c : Prop) : (term37 a c) = (term35 a c).
Proof. exact (eq_refl (term37 a c)). Qed.
Lemma lem3631494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3631495 (a : Prop) (c : Prop) : (term40 a c) = (term41 a c).
Proof. exact (MK_COMB (@lem3631494) (@lem3631493 a c)). Qed.
Lemma lem3631496 (a : Prop) : (term43 a) = (term43 a).
Proof. exact (eq_refl (term43 a)). Qed.
Lemma lem3631497 (c : Prop) (a : Prop) : ((term37 a c) = (term43 a)) = ((term35 a c) = (term43 a)).
Proof. exact (MK_COMB (@lem3631495 a c) (@lem3631496 a)). Qed.
Lemma lem3631498 (c : Prop) (a : Prop) : ((term37 a c) = (term42 a)) = ((term35 a c) = (term43 a)).
Proof. exact (TRANS (@lem3631492 c a) (@lem3631497 c a)). Qed.
Lemma lem3631499 (a : Prop) (c : Prop) (h1 : c = False) : (term35 a c) = (term43 a).
Proof. exact (EQ_MP (@lem3631498 c a) (@lem3631489 a c h1)). Qed.
Lemma lem3631500 (a : Prop) (c : Prop) (h1 : c = False) : (term43 a) = (term35 a c).
Proof. exact (SYM (@lem3631499 a c h1)). Qed.
Lemma lem3631506 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3631507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631508 : term44 = (imp False).
Proof. exact (MK_COMB (@lem3631507) (@lem3631506)). Qed.
Lemma lem3631509 (a : Prop) : (~ a) = (~ a).
Proof. exact (eq_refl (~ a)). Qed.
Lemma lem3631510 (a : Prop) : (term45 a) = (term46 a).
Proof. exact (MK_COMB (@lem3631508) (@lem3631509 a)). Qed.
Lemma lem3631512 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3631513 (a : Prop) : (term46 a) = True.
Proof. exact (@lem3631512 (~ a)). Qed.
Lemma lem3631514 (a : Prop) : (term45 a) = True.
Proof. exact (TRANS (@lem3631510 a) (@lem3631513 a)). Qed.
Lemma lem3631515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631516 (a : Prop) : (term47 a) = (imp True).
Proof. exact (MK_COMB (@lem3631515) (@lem3631514 a)). Qed.
Lemma lem3631518 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3631519 (a : Prop) : (a -> True) = True.
Proof. exact (@lem3631518 a). Qed.
Lemma lem3631520 (a : Prop) : (term39 a) = (True -> True).
Proof. exact (MK_COMB (@lem3631516 a) (@lem3631519 a)). Qed.
Lemma lem3631522 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3631523 : (True -> True) = True.
Proof. exact (@lem3631522 True). Qed.
Lemma lem3631524 (a : Prop) : (term39 a) = True.
Proof. exact (TRANS (@lem3631520 a) (@lem3631523)). Qed.
Lemma lem3631525 (a : Prop) : True = (term39 a).
Proof. exact (SYM (@lem3631524 a)). Qed.
Lemma lem3631526 (a : Prop) : term39 a.
Proof. exact (EQ_MP (@lem3631525 a) (@lem0)). Qed.
Lemma lem3631532 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3631533 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631534 : term48 = (imp True).
Proof. exact (MK_COMB (@lem3631533) (@lem3631532)). Qed.
Lemma lem3631535 (a : Prop) : (~ a) = (~ a).
Proof. exact (eq_refl (~ a)). Qed.
Lemma lem3631536 (a : Prop) : (term49 a) = (term50 a).
Proof. exact (MK_COMB (@lem3631534) (@lem3631535 a)). Qed.
Lemma lem3631538 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3631539 (a : Prop) : (term50 a) = (~ a).
Proof. exact (@lem3631538 (~ a)). Qed.
Lemma lem3631540 (a : Prop) : (term49 a) = (~ a).
Proof. exact (TRANS (@lem3631536 a) (@lem3631539 a)). Qed.
Lemma lem3631541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631542 (a : Prop) : (term51 a) = (term28 a).
Proof. exact (MK_COMB (@lem3631541) (@lem3631540 a)). Qed.
Lemma lem3631544 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3631545 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem3631544 a). Qed.
Lemma lem3631546 (a : Prop) : (term43 a) = (term52 a).
Proof. exact (MK_COMB (@lem3631542 a) (@lem3631545 a)). Qed.
Lemma lem3631548 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3631549 (a : Prop) : (term52 a) = True.
Proof. exact (@lem3631548 (~ a)). Qed.
Lemma lem3631550 (a : Prop) : (term43 a) = True.
Proof. exact (TRANS (@lem3631546 a) (@lem3631549 a)). Qed.
Lemma lem3631551 (a : Prop) : True = (term43 a).
Proof. exact (SYM (@lem3631550 a)). Qed.
Lemma lem3631552 (a : Prop) : term43 a.
Proof. exact (EQ_MP (@lem3631551 a) (@lem0)). Qed.
Lemma lem3631553 (a : Prop) (c : Prop) (h1 : c = False) : term35 a c.
Proof. exact (EQ_MP (@lem3631500 a c h1) (@lem3631552 a)). Qed.
Lemma lem3631554 (a : Prop) (c : Prop) (h1 : c = True) : term35 a c.
Proof. exact (EQ_MP (@lem3631487 a c h1) (@lem3631526 a)). Qed.
Lemma lem3631556 (a : Prop) (c : Prop) : term35 a c.
Proof. exact (or_elim (@lem3631464 c) (fun h0 : c = True => @lem3631554 a c h0) (fun h0 : c = False => @lem3631553 a c h0)). Qed.
Lemma lem3631557 (a : Prop) (c : Prop) : term20 a c.
Proof. exact (EQ_MP (@lem3631461 a c) (@lem3631556 a c)). Qed.
Lemma lem3631563 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3631564 (c : Prop) : (term53 c) = False.
Proof. exact (@lem3631563 (~ c)). Qed.
Lemma lem3631565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631566 (c : Prop) : (term54 c) = (imp False).
Proof. exact (MK_COMB (@lem3631565) (@lem3631564 c)). Qed.
Lemma lem3631567 (a : Prop) : (~ a) = (~ a).
Proof. exact (eq_refl (~ a)). Qed.
Lemma lem3631568 (c : Prop) (a : Prop) : (term55 c a) = (term46 a).
Proof. exact (MK_COMB (@lem3631566 c) (@lem3631567 a)). Qed.
Lemma lem3631570 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3631571 (a : Prop) : (term46 a) = True.
Proof. exact (@lem3631570 (~ a)). Qed.
Lemma lem3631572 (c : Prop) (a : Prop) : (term55 c a) = True.
Proof. exact (TRANS (@lem3631568 c a) (@lem3631571 a)). Qed.
Lemma lem3631573 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631574 (c : Prop) (a : Prop) : (term56 c a) = (imp True).
Proof. exact (MK_COMB (@lem3631573) (@lem3631572 c a)). Qed.
Lemma lem3631578 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3631579 (a : Prop) : (a /\ False) = False.
Proof. exact (@lem3631578 a). Qed.
Lemma lem3631580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631581 (a : Prop) : (term57 a) = (imp False).
Proof. exact (MK_COMB (@lem3631580) (@lem3631579 a)). Qed.
Lemma lem3631582 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3631583 (a : Prop) (c : Prop) : (term58 a c) = (False -> c).
Proof. exact (MK_COMB (@lem3631581 a) (@lem3631582 c)). Qed.
Lemma lem3631585 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3631586 (c : Prop) : (False -> c) = True.
Proof. exact (@lem3631585 c). Qed.
Lemma lem3631587 (a : Prop) (c : Prop) : (term58 a c) = True.
Proof. exact (TRANS (@lem3631583 a c) (@lem3631586 c)). Qed.
Lemma lem3631588 (a : Prop) (c : Prop) : (term25 a c) = (True -> True).
Proof. exact (MK_COMB (@lem3631574 c a) (@lem3631587 a c)). Qed.
Lemma lem3631590 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3631591 : (True -> True) = True.
Proof. exact (@lem3631590 True). Qed.
Lemma lem3631592 (a : Prop) (c : Prop) : (term25 a c) = True.
Proof. exact (TRANS (@lem3631588 a c) (@lem3631591)). Qed.
Lemma lem3631593 (a : Prop) (c : Prop) : True = (term25 a c).
Proof. exact (SYM (@lem3631592 a c)). Qed.
Lemma lem3631594 (a : Prop) (c : Prop) : term25 a c.
Proof. exact (EQ_MP (@lem3631593 a c) (@lem0)). Qed.
Lemma lem3631595 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : term22 a b c.
Proof. exact (EQ_MP (@lem3631431 a c b h1) (@lem3631594 a c)). Qed.
Lemma lem3631596 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : term22 a b c.
Proof. exact (EQ_MP (@lem3631418 a c b h1) (@lem3631557 a c)). Qed.
Lemma lem3631599 (a : Prop) (b : Prop) (c : Prop) : term22 a b c.
Proof. exact (or_elim (@lem3631391 b) (fun h0 : b = True => @lem3631596 a c b h0) (fun h0 : b = False => @lem3631595 a c b h0)). Qed.
Lemma lem3631600 (a : Prop) (b : Prop) (c : Prop) (h1 : term22 a b c) : term22 a b c.
Proof. exact (h1). Qed.
Lemma lem3631601 (b : Prop) (c : Prop) (a : Prop) (h1 : term59 b c a) : term59 b c a.
Proof. exact (h1). Qed.
Lemma lem3631602 (a : Prop) (b : Prop) (c : Prop) (h1 : term59 b c a) (h2 : term22 a b c) : term60 a b c.
Proof. exact (@lem3631600 a b c h2 (@lem3631601 b c a h1)). Qed.
Lemma lem3631603 (b : Prop) (c : Prop) (a : Prop) (h1 : term59 b c a) : term61 a b c.
Proof. exact (fun h0 : term22 a b c => @lem3631602 a b c h1 h0). Qed.
Lemma lem3631604 (a : Prop) (b : Prop) (c : Prop) (h1 : term22 a b c) : term22 a b c.
Proof. exact (h1). Qed.
Lemma lem3631605 (a : Prop) (b : Prop) (c : Prop) (h1 : term59 b c a) (h2 : term22 a b c) : term60 a b c.
Proof. exact (@lem3631603 b c a h1 (@lem3631604 a b c h2)). Qed.
Lemma lem3631606 (a : Prop) (b : Prop) (c : Prop) (h1 : term22 a b c) : term22 a b c.
Proof. exact (fun h0 : term59 b c a => @lem3631605 a b c h0 h1). Qed.
Lemma lem3631607 (a : Prop) (b : Prop) (c : Prop) : term62 a b c.
Proof. exact (fun h0 : term22 a b c => @lem3631606 a b c h0). Qed.
Lemma lem3631610 (a : Prop) (b : Prop) (c : Prop) : term22 a b c.
Proof. exact (@lem3631607 a b c (@lem3631599 a b c)). Qed.
Lemma lem3631611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term63 A s t.
Proof. exact (@lem3631610 (@INFINITE A s) (@FINITE A t) (term64 A s t)). Qed.
Lemma lem3631617 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term14 A s).
Proof. exact (EQ_MP (@lem3631375 A s) (@lem3631374 A s)). Qed.
Lemma lem3631618 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term14 A s).
Proof. exact (@lem3631617 A s). Qed.
Lemma lem3631619 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term65 A s t).
Proof. exact (@lem3631618 A (@DIFF A s t)). Qed.
Lemma lem3631620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3631621 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term66 A s t) = (term67 A s t).
Proof. exact (MK_COMB (@lem3631620) (@lem3631619 A s t)). Qed.
Lemma lem3631623 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3631624 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term69 A s t).
Proof. exact (@lem3631623 (term69 A s t)). Qed.
Lemma lem3631625 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term66 A s t) = (term69 A s t).
Proof. exact (TRANS (@lem3631621 A s t) (@lem3631624 A s t)). Qed.
Lemma lem3631626 {A : Type'} (t : A -> Prop) : (term70 A t) = (term70 A t).
Proof. exact (eq_refl (term70 A t)). Qed.
Lemma lem3631627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term71 A s t) = (term72 A s t).
Proof. exact (MK_COMB (@lem3631626 A t) (@lem3631625 A s t)). Qed.
Lemma lem3631630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631631 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term74 A s t).
Proof. exact (MK_COMB (@lem3631630) (@lem3631627 A s t)). Qed.
Lemma lem3631633 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term14 A s).
Proof. exact (EQ_MP (@lem3631375 A s) (@lem3631374 A s)). Qed.
Lemma lem3631634 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term14 A s).
Proof. exact (@lem3631633 A s). Qed.
Lemma lem3631635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3631636 {A : Type'} (s : A -> Prop) : (term75 A s) = (term76 A s).
Proof. exact (MK_COMB (@lem3631635) (@lem3631634 A s)). Qed.
Lemma lem3631638 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3631639 {A : Type'} (s : A -> Prop) : (term76 A s) = (@FINITE A s).
Proof. exact (@lem3631638 (@FINITE A s)). Qed.
Lemma lem3631640 {A : Type'} (s : A -> Prop) : (term75 A s) = (@FINITE A s).
Proof. exact (TRANS (@lem3631636 A s) (@lem3631639 A s)). Qed.
Lemma lem3631641 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term77 A t s) = (term78 A t s).
Proof. exact (MK_COMB (@lem3631631 A s t) (@lem3631640 A s)). Qed.
Lemma lem3631644 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term77 A t s).
Proof. exact (SYM (@lem3631641 A t s)). Qed.
Lemma lem3631645 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term72 A s t) : term72 A s t.
Proof. exact (h1). Qed.
Lemma lem3631646 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term69 A s t) : term69 A s t.
Proof. exact (h1). Qed.
Lemma lem3631647 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem3631649 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3631372 A s) (@lem3631371 A s)). Qed.
Lemma lem3631650 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3631649 A s). Qed.
Lemma lem3631651 {A : Type'} (s : A -> Prop) : term79 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem3631652 {A : Type'} (s : A -> Prop) : (term79 A s) = (term80 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem3631653 {A : Type'} (s : A -> Prop) : term80 A s.
Proof. exact (EQ_MP (@lem3631652 A s) (@lem3631651 A s)). Qed.
Lemma lem3631654 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term81 A s t.
Proof. exact (@lem3631653 A s t). Qed.
Lemma lem3631655 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = ((term82 A s t) = (term83 A s t)).
Proof. exact (eq_refl (term81 A s t)). Qed.
Lemma lem3631657 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem3631659 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term69 A s t) = ((term69 A s t) = True).
Proof. exact (@lem7 (term69 A s t)). Qed.
Lemma lem3631664 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term83 A s t).
Proof. exact (EQ_MP (@lem3631655 A s t) (@lem3631654 A s t)). Qed.
Lemma lem3631665 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term83 A s t).
Proof. exact (@lem3631664 A s t). Qed.
Lemma lem3631666 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term72 A s t).
Proof. exact (@lem3631665 A t (@DIFF A s t)). Qed.
Lemma lem3631670 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem3631657 A t) (@lem3631647 A t h1)). Qed.
Lemma lem3631671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3631672 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (term70 A t) = (and True).
Proof. exact (MK_COMB (@lem3631671) (@lem3631670 A t h1)). Qed.
Lemma lem3631674 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term69 A s t) : (term69 A s t) = True.
Proof. exact (EQ_MP (@lem3631659 A s t) (@lem3631646 A s t h1)). Qed.
Lemma lem3631675 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term72 A s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3631672 A t h1) (@lem3631674 A s t h2)). Qed.
Lemma lem3631677 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3631678 : (True /\ True) = True.
Proof. exact (@lem3631677 True). Qed.
Lemma lem3631679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term72 A s t) = True.
Proof. exact (TRANS (@lem3631675 A s t h1 h2) (@lem3631678)). Qed.
Lemma lem3631680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term84 A s t) = True.
Proof. exact (TRANS (@lem3631666 A s t) (@lem3631679 A s t h1 h2)). Qed.
Lemma lem3631681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3631682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term85 A s t) = (and True).
Proof. exact (MK_COMB (@lem3631681) (@lem3631680 A s t h1 h2)). Qed.
Lemma lem3631683 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (eq_refl (term86 A s t)). Qed.
Lemma lem3631684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term87 A s t) = (term88 A s t).
Proof. exact (MK_COMB (@lem3631682 A s t h1 h2) (@lem3631683 A s t)). Qed.
Lemma lem3631686 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3631687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term86 A s t).
Proof. exact (@lem3631686 (term86 A s t)). Qed.
Lemma lem3631688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term87 A s t) = (term86 A s t).
Proof. exact (TRANS (@lem3631684 A s t h1 h2) (@lem3631687 A s t)). Qed.
Lemma lem3631689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term86 A s t) = (term87 A s t).
Proof. exact (SYM (@lem3631688 A s t h1 h2)). Qed.
Lemma lem3631691 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term89 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3631692 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term89 A s t).
Proof. exact (@lem3631691 A s t). Qed.
Lemma lem3631693 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term90 A s t).
Proof. exact (@lem3631692 A s (term91 A s t)). Qed.
Lemma lem3631700 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term86 A s t).
Proof. exact (SYM (@lem3631693 A s t)). Qed.
Lemma lem3631708 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3631709 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3631708 A P x). Qed.
Lemma lem3631710 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3631709 A s x). Qed.
Lemma lem3631711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3631712 {A : Type'} (s : A -> Prop) (x : A) : (term92 A x s) = (term93 A s x).
Proof. exact (MK_COMB (@lem3631711) (@lem3631710 A s x)). Qed.
Lemma lem3631714 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term94 A x s t) = (term95 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3631715 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term94 A x s t) = (term95 A s x t).
Proof. exact (@lem3631714 A s x t). Qed.
Lemma lem3631716 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term96 A x s t) = (term97 A x s t).
Proof. exact (@lem3631715 A t x (@DIFF A s t)). Qed.
Lemma lem3631720 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3631721 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3631720 A P x). Qed.
Lemma lem3631722 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3631721 A t x). Qed.
Lemma lem3631723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3631724 {A : Type'} (t : A -> Prop) (x : A) : (term98 A x t) = (term99 A t x).
Proof. exact (MK_COMB (@lem3631723) (@lem3631722 A t x)). Qed.
Lemma lem3631726 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term100 A x s t) = (term101 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3631727 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term100 A x s t) = (term101 A s x t).
Proof. exact (@lem3631726 A s x t). Qed.
Lemma lem3631731 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3631732 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3631731 A P x). Qed.
Lemma lem3631733 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3631732 A s x). Qed.
Lemma lem3631734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3631735 {A : Type'} (s : A -> Prop) (x : A) : (term102 A x s) = (term103 A s x).
Proof. exact (MK_COMB (@lem3631734) (@lem3631733 A s x)). Qed.
Lemma lem3631737 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3631738 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3631737 A P x). Qed.
Lemma lem3631739 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3631738 A t x). Qed.
Lemma lem3631740 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3631741 {A : Type'} (t : A -> Prop) (x : A) : (term104 A x t) = (term105 A t x).
Proof. exact (MK_COMB (@lem3631740) (@lem3631739 A t x)). Qed.
Lemma lem3631742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term101 A s x t) = (term106 A s t x).
Proof. exact (MK_COMB (@lem3631735 A s x) (@lem3631741 A t x)). Qed.
Lemma lem3631745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term100 A x s t) = (term106 A s t x).
Proof. exact (TRANS (@lem3631727 A s x t) (@lem3631742 A s t x)). Qed.
Lemma lem3631746 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term97 A x s t) = (term107 A s t x).
Proof. exact (MK_COMB (@lem3631724 A t x) (@lem3631745 A s t x)). Qed.
Lemma lem3631749 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term96 A x s t) = (term107 A s t x).
Proof. exact (TRANS (@lem3631716 A x s t) (@lem3631746 A s t x)). Qed.
Lemma lem3631750 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term108 A x s t) = (term109 A s t x).
Proof. exact (MK_COMB (@lem3631712 A s x) (@lem3631749 A s t x)). Qed.
Lemma lem3631753 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term110 A s t) = (term111 A s t).
Proof. exact (fun_ext (fun x : A => @lem3631750 A s t x)). Qed.
Lemma lem3631754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3631755 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term112 A s t).
Proof. exact (MK_COMB (@lem3631754 A) (@lem3631753 A s t)). Qed.
Lemma lem3631760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term90 A s t).
Proof. exact (SYM (@lem3631755 A s t)). Qed.
Lemma lem3631762 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3631763 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term114 A s t).
Proof. exact (@lem3631762 (term112 A s t)). Qed.
Lemma lem3631764 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term112 A s t).
Proof. exact (SYM (@lem3631763 A s t)). Qed.
Lemma lem3631765 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term115 A s t) : term115 A s t.
Proof. exact (h1). Qed.
Lemma lem3631768 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term114 A s t) : term114 A s t.
Proof. exact (h1). Qed.
Lemma lem3631769 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term116 A s t.
Proof. exact (fun h0 : term114 A s t => @lem3631768 A s t h0). Qed.
Lemma lem3631770 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term116 A s t) : term116 A s t.
Proof. exact (h1). Qed.
Lemma lem3631771 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term114 A s t) : term114 A s t.
Proof. exact (h1). Qed.
Lemma lem3631772 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term114 A s t) (h2 : term116 A s t) : term114 A s t.
Proof. exact (@lem3631770 A s t h2 (@lem3631771 A s t h1)). Qed.
Lemma lem3631773 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term114 A s t) : term117 A s t.
Proof. exact (fun h0 : term116 A s t => @lem3631772 A s t h1 h0). Qed.
Lemma lem3631774 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term116 A s t) : term116 A s t.
Proof. exact (h1). Qed.
Lemma lem3631775 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term114 A s t) (h2 : term116 A s t) : term114 A s t.
Proof. exact (@lem3631773 A s t h1 (@lem3631774 A s t h2)). Qed.
Lemma lem3631776 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term116 A s t) : term116 A s t.
Proof. exact (fun h0 : term114 A s t => @lem3631775 A s t h0 h1). Qed.
Lemma lem3631777 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term118 A s t.
Proof. exact (fun h0 : term116 A s t => @lem3631776 A s t h0). Qed.
Lemma lem3631780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term116 A s t.
Proof. exact (@lem3631777 A s t (@lem3631769 A s t)). Qed.
Lemma lem3631781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term116 A s t.
Proof. exact (@lem3631780 A s t). Qed.
Lemma lem3631791 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3631792 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term119 A s t).
Proof. exact (@lem3631791 (term115 A s t)). Qed.
Lemma lem3631794 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3631795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term119 A s t) = (term112 A s t).
Proof. exact (@lem3631794 (term112 A s t)). Qed.
Lemma lem3631800 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term112 A s t).
Proof. exact (TRANS (@lem3631792 A s t) (@lem3631795 A s t)). Qed.
Lemma lem3631807 {A : Type'} (t : A -> Prop) : (term120 A t) = (term121 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3631800 A s t)). Qed.
Lemma lem3631808 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3631809 {A : Type'} (t : A -> Prop) : (term122 A t) = (term123 A t).
Proof. exact (MK_COMB (@lem3631808 A) (@lem3631807 A t)). Qed.
Lemma lem3631814 {A : Type'} : (term124 A) = (term125 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3631809 A t)). Qed.
Lemma lem3631815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3631824 {A : Type'} : (term126 A) = (term127 A).
Proof. exact (MK_COMB (@lem3631815 A) (@lem3631814 A)). Qed.
Lemma lem3631839 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term109 A s t x) = (term109 A s t x).
Proof. exact (eq_refl (term109 A s t x)). Qed.
Lemma lem3631840 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (fun_ext (fun x : A => @lem3631839 A s t x)). Qed.
Lemma lem3631841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3631842 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term112 A s t).
Proof. exact (MK_COMB (@lem3631841 A) (@lem3631840 A s t)). Qed.
Lemma lem3631843 {A : Type'} (t : A -> Prop) : (term121 A t) = (term121 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3631842 A s t)). Qed.
Lemma lem3631844 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3631845 {A : Type'} (t : A -> Prop) : (term123 A t) = (term123 A t).
Proof. exact (MK_COMB (@lem3631844 A) (@lem3631843 A t)). Qed.
Lemma lem3631846 {A : Type'} : (term125 A) = (term125 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3631845 A t)). Qed.
Lemma lem3631847 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3631848 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (MK_COMB (@lem3631847 A) (@lem3631846 A)). Qed.
Lemma lem3631875 {A : Type'} : (term126 A) = (term127 A).
Proof. exact (TRANS (@lem3631824 A) (@lem3631848 A)). Qed.
Lemma lem3631876 {A : Type'} : (term127 A) = (term126 A).
Proof. exact (SYM (@lem3631875 A)). Qed.
Lemma lem3631879 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3631880 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term128 A s t x).
Proof. exact (@lem3631879 (term107 A s t x)). Qed.
Lemma lem3631881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term128 A s t x) = (term107 A s t x).
Proof. exact (SYM (@lem3631880 A s t x)). Qed.
Lemma lem3631882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) : term129 A s t x.
Proof. exact (h1). Qed.
Lemma lem3631888 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3631893 {A : Type'} (t : A -> Prop) (x : A) : (term130 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3631895 {A : Type'} (s : A -> Prop) (x : A) : (term131 A s x) = (term131 A s x).
Proof. exact (eq_refl (term131 A s x)). Qed.
Lemma lem3631896 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term132 A s t x) = (term133 A s t x).
Proof. exact (MK_COMB (@lem3631895 A s x) (@lem3631893 A t x)). Qed.
Lemma lem3631897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term134 A s t x) = (term132 A s t x).
Proof. exact (@lem17045 (s x) (term105 A t x)). Qed.
Lemma lem3631898 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term134 A s t x) = (term133 A s t x).
Proof. exact (TRANS (@lem3631897 A s t x) (@lem3631896 A s t x)). Qed.
Lemma lem3631900 {A : Type'} (t : A -> Prop) (x : A) : (term135 A t x) = (term135 A t x).
Proof. exact (eq_refl (term135 A t x)). Qed.
Lemma lem3631901 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term136 A s t x) = (term137 A s t x).
Proof. exact (MK_COMB (@lem3631900 A t x) (@lem3631898 A s t x)). Qed.
Lemma lem3631902 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term129 A s t x) = (term136 A s t x).
Proof. exact (@lem17160 (t x) (term106 A s t x)). Qed.
Lemma lem3631907 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term129 A s t x) = (term137 A s t x).
Proof. exact (TRANS (@lem3631902 A s t x) (@lem3631901 A s t x)). Qed.
Lemma lem3631912 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3631932 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) : term137 A s t x.
Proof. exact (EQ_MP (@lem3631907 A s t x) (@lem3631882 A s t x h1)). Qed.
Lemma lem3631933 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) : term133 A s t x.
Proof. exact (proj2 (@lem3631932 A s t x h1)). Qed.
Lemma lem3631940 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3631948 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) : term105 A s x.
Proof. exact (h1). Qed.
Lemma lem3631960 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3631962 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3631966 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) : term105 A s x.
Proof. exact (h1). Qed.
Lemma lem3631970 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) : term105 A t x.
Proof. exact (proj1 (@lem3631932 A s t x h1)). Qed.
Lemma lem3631972 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3631974 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3631975 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term138 A s x.
Proof. exact (fun h0 : term105 A s x => @lem3631974 A s x h1). Qed.
Lemma lem3631977 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3631978 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (s x).
Proof. exact (@lem3631977 (s x)). Qed.
Lemma lem3631979 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3631978 A s x) (@lem3631975 A s x h1)). Qed.
Lemma lem3631982 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3631984 {A : Type'} (s : A -> Prop) (x : A) : (term105 A s x) = (term140 A s x).
Proof. exact (@lem3631982 (s x)). Qed.
Lemma lem3631987 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) : term140 A s x.
Proof. exact (EQ_MP (@lem3631984 A s x) (@lem3631966 A s x h1)). Qed.
Lemma lem3631990 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (@lem3631987 A s x h1 (@lem3631979 A s x h2)). Qed.
Lemma lem3631991 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : term141.
Proof. exact (fun h0 : ~ False => @lem3631990 A s x h1 h2). Qed.
Lemma lem3631993 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3631994 : term141 = False.
Proof. exact (@lem3631993 False). Qed.
Lemma lem3631995 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3631994) (@lem3631991 A s x h1 h2)). Qed.
Lemma lem3631997 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3631998 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term138 A t x.
Proof. exact (fun h0 : term105 A t x => @lem3631997 A t x h1). Qed.
Lemma lem3632000 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3632001 {A : Type'} (t : A -> Prop) (x : A) : (term138 A t x) = (t x).
Proof. exact (@lem3632000 (t x)). Qed.
Lemma lem3632002 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3632001 A t x) (@lem3631998 A t x h1)). Qed.
Lemma lem3632005 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3632007 {A : Type'} (t : A -> Prop) (x : A) : (term105 A t x) = (term140 A t x).
Proof. exact (@lem3632005 (t x)). Qed.
Lemma lem3632010 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) : term140 A t x.
Proof. exact (EQ_MP (@lem3632007 A t x) (@lem3631970 A s t x h1)). Qed.
Lemma lem3632013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : False.
Proof. exact (@lem3632010 A s t x h1 (@lem3632002 A t x h2)). Qed.
Lemma lem3632014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : term141.
Proof. exact (fun h0 : ~ False => @lem3632013 A s t x h1 h2). Qed.
Lemma lem3632016 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3632017 : term141 = False.
Proof. exact (@lem3632016 False). Qed.
Lemma lem3632018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3632017) (@lem3632014 A s t x h1 h2)). Qed.
Lemma lem3632019 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3632018 A s t x h1 h2) (fun h3 : False => @lem3631972 A t x h2)). Qed.
Lemma lem3632020 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3632019 A s t x h1 h2) (@lem3631972 A t x h2)). Qed.
Lemma lem3632021 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : (term105 A s x) = False.
Proof. exact (prop_ext (fun h3 : term105 A s x => @lem3631995 A s x h1 h2) (fun h3 : False => @lem3631966 A s x h1)). Qed.
Lemma lem3632022 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632021 A s x h1 h2) (@lem3631966 A s x h1)). Qed.
Lemma lem3632023 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3632022 A s x h1 h2) (fun h3 : False => @lem3631962 A s x h2)). Qed.
Lemma lem3632024 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632023 A s x h1 h2) (@lem3631962 A s x h2)). Qed.
Lemma lem3632025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3632020 A s t x h1 h2) (fun h3 : False => @lem3631960 A t x h2)). Qed.
Lemma lem3632026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3632025 A s t x h1 h2) (@lem3631960 A t x h2)). Qed.
Lemma lem3632027 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : (term105 A s x) = False.
Proof. exact (prop_ext (fun h3 : term105 A s x => @lem3632024 A s x h1 h2) (fun h3 : False => @lem3631948 A s x h1)). Qed.
Lemma lem3632028 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632027 A s x h1 h2) (@lem3631948 A s x h1)). Qed.
Lemma lem3632029 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3632028 A s x h1 h2) (fun h3 : False => @lem3631940 A s x h2)). Qed.
Lemma lem3632030 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632029 A s x h1 h2) (@lem3631940 A s x h2)). Qed.
Lemma lem3632031 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3632026 A s t x h1 h2) (fun h3 : False => @lem3631960 A t x h2)). Qed.
Lemma lem3632032 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3632031 A s t x h1 h2) (@lem3631960 A t x h2)). Qed.
Lemma lem3632033 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : (term105 A s x) = False.
Proof. exact (prop_ext (fun h3 : term105 A s x => @lem3632030 A s x h1 h2) (fun h3 : False => @lem3631948 A s x h1)). Qed.
Lemma lem3632034 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632033 A s x h1 h2) (@lem3631948 A s x h1)). Qed.
Lemma lem3632035 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3632034 A s x h1 h2) (fun h3 : False => @lem3631940 A s x h2)). Qed.
Lemma lem3632036 {A : Type'} (s : A -> Prop) (x : A) (h1 : term105 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632035 A s x h1 h2) (@lem3631940 A s x h2)). Qed.
Lemma lem3632037 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : False.
Proof. exact (or_elim (@lem3631933 A s t x h1) (fun h0 : term105 A s x => @lem3632036 A s x h0 h2) (fun h0 : t x => @lem3632032 A s t x h1 h0)). Qed.
Lemma lem3632038 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3632037 A t s x h1 h2) (fun h3 : False => @lem3631912 A s x h2)). Qed.
Lemma lem3632039 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632038 A t s x h1 h2) (@lem3631912 A s x h2)). Qed.
Lemma lem3632040 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3632039 A t s x h1 h2) (fun h3 : False => @lem3631888 A s x h2)). Qed.
Lemma lem3632041 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632040 A t s x h1 h2) (@lem3631888 A s x h2)). Qed.
Lemma lem3632042 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : (term129 A s t x) = False.
Proof. exact (prop_ext (fun h3 : term129 A s t x => @lem3632041 A t s x h1 h2) (fun h3 : False => @lem3631882 A s t x h1)). Qed.
Lemma lem3632043 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term129 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3632042 A t s x h1 h2) (@lem3631882 A s t x h1)). Qed.
Lemma lem3632044 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) : term128 A s t x.
Proof. exact (fun h0 : term129 A s t x => @lem3632043 A t s x h0 h1). Qed.
Lemma lem3632045 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) : term107 A s t x.
Proof. exact (EQ_MP (@lem3631881 A s t x) (@lem3632044 A t s x h1)). Qed.
Lemma lem3632046 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term109 A s t x.
Proof. exact (fun h0 : s x => @lem3632045 A t s x h0). Qed.
Lemma lem3632051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term112 A s t.
Proof. exact (fun x : A => @lem3632046 A s t x). Qed.
Lemma lem3632056 {A : Type'} (t : A -> Prop) : term123 A t.
Proof. exact (fun s : A -> Prop => @lem3632051 A s t). Qed.
Lemma lem3632061 {A : Type'} : term127 A.
Proof. exact (fun t : A -> Prop => @lem3632056 A t). Qed.
Lemma lem3632062 {A : Type'} : term126 A.
Proof. exact (EQ_MP (@lem3631876 A) (@lem3632061 A)). Qed.
Lemma lem3632063 {A : Type'} (t : A -> Prop) : term142 A t.
Proof. exact (@lem3632062 A t). Qed.
Lemma lem3632064 {A : Type'} (t : A -> Prop) : (term142 A t) = (term122 A t).
Proof. exact (eq_refl (term142 A t)). Qed.
Lemma lem3632065 {A : Type'} (t : A -> Prop) : term122 A t.
Proof. exact (EQ_MP (@lem3632064 A t) (@lem3632063 A t)). Qed.
Lemma lem3632066 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term143 A t s.
Proof. exact (@lem3632065 A t s). Qed.
Lemma lem3632067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A t s) = (term114 A s t).
Proof. exact (eq_refl (term143 A t s)). Qed.
Lemma lem3632068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term114 A s t.
Proof. exact (EQ_MP (@lem3632067 A s t) (@lem3632066 A t s)). Qed.
Lemma lem3632070 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term114 A s t.
Proof. exact (@lem3631781 A s t (@lem3632068 A s t)). Qed.
Lemma lem3632071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term115 A s t) : False.
Proof. exact (@lem3632070 A s t (@lem3631765 A s t h1)). Qed.
Lemma lem3632072 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term115 A s t) : (term115 A s t) = False.
Proof. exact (prop_ext (fun h2 : term115 A s t => @lem3632071 A s t h1) (fun h2 : False => @lem3631765 A s t h1)). Qed.
Lemma lem3632073 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term115 A s t) : False.
Proof. exact (EQ_MP (@lem3632072 A s t h1) (@lem3631765 A s t h1)). Qed.
Lemma lem3632074 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term114 A s t.
Proof. exact (fun h0 : term115 A s t => @lem3632073 A s t h0). Qed.
Lemma lem3632075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term112 A s t.
Proof. exact (EQ_MP (@lem3631764 A s t) (@lem3632074 A s t)). Qed.
Lemma lem3632076 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term90 A s t.
Proof. exact (EQ_MP (@lem3631760 A s t) (@lem3632075 A s t)). Qed.
Lemma lem3632077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term86 A s t.
Proof. exact (EQ_MP (@lem3631700 A s t) (@lem3632076 A s t)). Qed.
Lemma lem3632078 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : term87 A s t.
Proof. exact (EQ_MP (@lem3631689 A s t h1 h2) (@lem3632077 A s t)). Qed.
Lemma lem3632079 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : term7 A s.
Proof. exact (ex_intro (term8 A s) (term91 A s t) (@lem3632078 A s t h1 h2)). Qed.
Lemma lem3632080 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : @FINITE A s.
Proof. exact (@lem3631650 A s (@lem3632079 A s t h1 h2)). Qed.
Lemma lem3632081 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term72 A s t) : term69 A s t.
Proof. exact (proj2 (@lem3631645 A s t h1)). Qed.
Lemma lem3632082 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term72 A s t) : @FINITE A t.
Proof. exact (proj1 (@lem3631645 A s t h1)). Qed.
Lemma lem3632083 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (term69 A s t) = (@FINITE A s).
Proof. exact (prop_ext (fun h3 : term69 A s t => @lem3632080 A s t h1 h2) (fun h3 : @FINITE A s => @lem3631646 A s t h2)). Qed.
Lemma lem3632084 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem3632083 A s t h1 h2) (@lem3631646 A s t h2)). Qed.
Lemma lem3632085 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : (@FINITE A t) = (@FINITE A s).
Proof. exact (prop_ext (fun h3 : @FINITE A t => @lem3632084 A s t h1 h2) (fun h3 : @FINITE A s => @lem3631647 A t h1)). Qed.
Lemma lem3632086 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term69 A s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem3632085 A s t h1 h2) (@lem3631647 A t h1)). Qed.
Lemma lem3632087 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term72 A s t) : (term69 A s t) = (@FINITE A s).
Proof. exact (prop_ext (fun h3 : term69 A s t => @lem3632086 A s t h1 h3) (fun h3 : @FINITE A s => @lem3632081 A s t h2)). Qed.
Lemma lem3632088 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term72 A s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem3632087 A s t h1 h2) (@lem3632081 A s t h2)). Qed.
Lemma lem3632089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term72 A s t) : (@FINITE A t) = (@FINITE A s).
Proof. exact (prop_ext (fun h2 : @FINITE A t => @lem3632088 A s t h2 h1) (fun h2 : @FINITE A s => @lem3632082 A s t h1)). Qed.
Lemma lem3632090 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term72 A s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem3632089 A s t h1) (@lem3632082 A s t h1)). Qed.
Lemma lem3632091 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term78 A t s.
Proof. exact (fun h0 : term72 A s t => @lem3632090 A s t h0). Qed.
Lemma lem3632092 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term77 A t s.
Proof. exact (EQ_MP (@lem3631644 A t s) (@lem3632091 A t s)). Qed.
Lemma lem3632093 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term144 A s t.
Proof. exact (@lem3631611 A s t (@lem3632092 A t s)). Qed.
Lemma lem3632098 {A : Type'} (s : A -> Prop) : term145 A s.
Proof. exact (fun t : A -> Prop => @lem3632093 A s t). Qed.
Lemma lem3632103 {A : Type'} : term146 A.
Proof. exact (fun s : A -> Prop => @lem3632098 A s). Qed.
