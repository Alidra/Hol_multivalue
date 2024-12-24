Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_ELIM_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem13355 (c : Prop) : term0 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem13356 (c : Prop) : (term0 c) = (term1 c).
Proof. exact (eq_refl (term0 c)). Qed.
Lemma lem13357 (c : Prop) : term1 c.
Proof. exact (EQ_MP (@lem13356 c) (@lem13355 c)). Qed.
Lemma lem13358 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem13359 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem13360 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term2 A x P y) = (term2 A x P y).
Proof. exact (eq_refl (term2 A x P y)). Qed.
Lemma lem13361 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = True) : (term3 A x P y c) = (term4 A x P y).
Proof. exact (MK_COMB (@lem13360 A x P y) (@lem13358 c h1)). Qed.
Lemma lem13362 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term4 A x P y) = ((term5 A P x y) = (term6 A x P y)).
Proof. exact (eq_refl (term4 A x P y)). Qed.
Lemma lem13363 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) : (term7 A x P y c) = (term7 A x P y c).
Proof. exact (eq_refl (term7 A x P y c)). Qed.
Lemma lem13364 {A : Type'} (c : Prop) (x : A) (P : A -> Prop) (y : A) : ((term3 A x P y c) = (term4 A x P y)) = ((term3 A x P y c) = ((term5 A P x y) = (term6 A x P y))).
Proof. exact (MK_COMB (@lem13363 A x P y c) (@lem13362 A x P y)). Qed.
Lemma lem13365 {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A) : (term3 A x P y c) = ((term8 A P c x y) = (term9 A x c P y)).
Proof. exact (eq_refl (term3 A x P y c)). Qed.
Lemma lem13366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13367 {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A) : (term7 A x P y c) = (term10 A x c P y).
Proof. exact (MK_COMB (@lem13366) (@lem13365 A x c P y)). Qed.
Lemma lem13368 {A : Type'} (x : A) (P : A -> Prop) (y : A) : ((term5 A P x y) = (term6 A x P y)) = ((term5 A P x y) = (term6 A x P y)).
Proof. exact (eq_refl ((term5 A P x y) = (term6 A x P y))). Qed.
Lemma lem13369 {A : Type'} (c : Prop) (x : A) (P : A -> Prop) (y : A) : ((term3 A x P y c) = ((term5 A P x y) = (term6 A x P y))) = (((term8 A P c x y) = (term9 A x c P y)) = ((term5 A P x y) = (term6 A x P y))).
Proof. exact (MK_COMB (@lem13367 A x c P y) (@lem13368 A x P y)). Qed.
Lemma lem13370 {A : Type'} (c : Prop) (x : A) (P : A -> Prop) (y : A) : ((term3 A x P y c) = (term4 A x P y)) = (((term8 A P c x y) = (term9 A x c P y)) = ((term5 A P x y) = (term6 A x P y))).
Proof. exact (TRANS (@lem13364 A c x P y) (@lem13369 A c x P y)). Qed.
Lemma lem13371 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = True) : ((term8 A P c x y) = (term9 A x c P y)) = ((term5 A P x y) = (term6 A x P y)).
Proof. exact (EQ_MP (@lem13370 A c x P y) (@lem13361 A x P y c h1)). Qed.
Lemma lem13372 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = True) : ((term5 A P x y) = (term6 A x P y)) = ((term8 A P c x y) = (term9 A x c P y)).
Proof. exact (SYM (@lem13371 A x P y c h1)). Qed.
Lemma lem13373 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term2 A x P y) = (term2 A x P y).
Proof. exact (eq_refl (term2 A x P y)). Qed.
Lemma lem13374 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = False) : (term3 A x P y c) = (term11 A x P y).
Proof. exact (MK_COMB (@lem13373 A x P y) (@lem13359 c h1)). Qed.
Lemma lem13375 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term11 A x P y) = ((term12 A P x y) = (term13 A x P y)).
Proof. exact (eq_refl (term11 A x P y)). Qed.
Lemma lem13376 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) : (term7 A x P y c) = (term7 A x P y c).
Proof. exact (eq_refl (term7 A x P y c)). Qed.
Lemma lem13377 {A : Type'} (c : Prop) (x : A) (P : A -> Prop) (y : A) : ((term3 A x P y c) = (term11 A x P y)) = ((term3 A x P y c) = ((term12 A P x y) = (term13 A x P y))).
Proof. exact (MK_COMB (@lem13376 A x P y c) (@lem13375 A x P y)). Qed.
Lemma lem13378 {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A) : (term3 A x P y c) = ((term8 A P c x y) = (term9 A x c P y)).
Proof. exact (eq_refl (term3 A x P y c)). Qed.
Lemma lem13379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13380 {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A) : (term7 A x P y c) = (term10 A x c P y).
Proof. exact (MK_COMB (@lem13379) (@lem13378 A x c P y)). Qed.
Lemma lem13381 {A : Type'} (x : A) (P : A -> Prop) (y : A) : ((term12 A P x y) = (term13 A x P y)) = ((term12 A P x y) = (term13 A x P y)).
Proof. exact (eq_refl ((term12 A P x y) = (term13 A x P y))). Qed.
Lemma lem13382 {A : Type'} (c : Prop) (x : A) (P : A -> Prop) (y : A) : ((term3 A x P y c) = ((term12 A P x y) = (term13 A x P y))) = (((term8 A P c x y) = (term9 A x c P y)) = ((term12 A P x y) = (term13 A x P y))).
Proof. exact (MK_COMB (@lem13380 A x c P y) (@lem13381 A x P y)). Qed.
Lemma lem13383 {A : Type'} (c : Prop) (x : A) (P : A -> Prop) (y : A) : ((term3 A x P y c) = (term11 A x P y)) = (((term8 A P c x y) = (term9 A x c P y)) = ((term12 A P x y) = (term13 A x P y))).
Proof. exact (TRANS (@lem13377 A c x P y) (@lem13382 A c x P y)). Qed.
Lemma lem13384 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = False) : ((term8 A P c x y) = (term9 A x c P y)) = ((term12 A P x y) = (term13 A x P y)).
Proof. exact (EQ_MP (@lem13383 A c x P y) (@lem13374 A x P y c h1)). Qed.
Lemma lem13385 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = False) : ((term12 A P x y) = (term13 A x P y)) = ((term8 A P c x y) = (term9 A x c P y)).
Proof. exact (SYM (@lem13384 A x P y c h1)). Qed.
Lemma lem13389 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13390 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem13389 A t2 t1). Qed.
Lemma lem13391 {A : Type'} (y : A) (x : A) : (@COND A True x y) = x.
Proof. exact (@lem13390 A y x). Qed.
Lemma lem13392 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem13393 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term5 A P x y) = (P x).
Proof. exact (MK_COMB (@lem13392 A P) (@lem13391 A y x)). Qed.
Lemma lem13394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13395 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term14 A P x y) = (term15 A P x).
Proof. exact (MK_COMB (@lem13394) (@lem13393 A y P x)). Qed.
Lemma lem13399 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem13400 {A : Type'} (P : A -> Prop) (x : A) : (term16 A P x) = (P x).
Proof. exact (@lem13399 (P x)). Qed.
Lemma lem13401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13402 {A : Type'} (P : A -> Prop) (x : A) : (term17 A P x) = (term18 A P x).
Proof. exact (MK_COMB (@lem13401) (@lem13400 A P x)). Qed.
Lemma lem13406 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem13407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem13408 : term19 = (imp False).
Proof. exact (MK_COMB (@lem13407) (@lem13406)). Qed.
Lemma lem13409 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem13410 {A : Type'} (P : A -> Prop) (y : A) : (term20 A P y) = (term21 A P y).
Proof. exact (MK_COMB (@lem13408) (@lem13409 A P y)). Qed.
Lemma lem13412 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem13413 {A : Type'} (P : A -> Prop) (y : A) : (term21 A P y) = True.
Proof. exact (@lem13412 (P y)). Qed.
Lemma lem13414 {A : Type'} (P : A -> Prop) (y : A) : (term20 A P y) = True.
Proof. exact (TRANS (@lem13410 A P y) (@lem13413 A P y)). Qed.
Lemma lem13415 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term6 A x P y) = (term22 A P x).
Proof. exact (MK_COMB (@lem13402 A P x) (@lem13414 A P y)). Qed.
Lemma lem13417 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem13418 {A : Type'} (P : A -> Prop) (x : A) : (term22 A P x) = (P x).
Proof. exact (@lem13417 (P x)). Qed.
Lemma lem13419 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term6 A x P y) = (P x).
Proof. exact (TRANS (@lem13415 A y P x) (@lem13418 A P x)). Qed.
Lemma lem13420 {A : Type'} (y : A) (P : A -> Prop) (x : A) : ((term5 A P x y) = (term6 A x P y)) = ((P x) = (P x)).
Proof. exact (MK_COMB (@lem13395 A y P x) (@lem13419 A y P x)). Qed.
Lemma lem13422 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13423 (x : Prop) : (x = x) = True.
Proof. exact (@lem13422 Prop x). Qed.
Lemma lem13424 {A : Type'} (P : A -> Prop) (x : A) : ((P x) = (P x)) = True.
Proof. exact (@lem13423 (P x)). Qed.
Lemma lem13425 {A : Type'} (x : A) (P : A -> Prop) (y : A) : ((term5 A P x y) = (term6 A x P y)) = True.
Proof. exact (TRANS (@lem13420 A y P x) (@lem13424 A P x)). Qed.
Lemma lem13426 {A : Type'} (x : A) (P : A -> Prop) (y : A) : True = ((term5 A P x y) = (term6 A x P y)).
Proof. exact (SYM (@lem13425 A x P y)). Qed.
Lemma lem13427 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term5 A P x y) = (term6 A x P y).
Proof. exact (EQ_MP (@lem13426 A x P y) (@lem0)). Qed.
Lemma lem13431 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13432 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem13431 A t1 t2). Qed.
Lemma lem13433 {A : Type'} (x : A) (y : A) : (@COND A False x y) = y.
Proof. exact (@lem13432 A x y). Qed.
Lemma lem13434 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem13435 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term12 A P x y) = (P y).
Proof. exact (MK_COMB (@lem13434 A P) (@lem13433 A x y)). Qed.
Lemma lem13436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13437 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term23 A P x y) = (term15 A P y).
Proof. exact (MK_COMB (@lem13436) (@lem13435 A x P y)). Qed.
Lemma lem13441 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem13442 {A : Type'} (P : A -> Prop) (x : A) : (term21 A P x) = True.
Proof. exact (@lem13441 (P x)). Qed.
Lemma lem13443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13444 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (and True).
Proof. exact (MK_COMB (@lem13443) (@lem13442 A P x)). Qed.
Lemma lem13448 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem13449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem13450 : term25 = (imp True).
Proof. exact (MK_COMB (@lem13449) (@lem13448)). Qed.
Lemma lem13451 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem13452 {A : Type'} (P : A -> Prop) (y : A) : (term26 A P y) = (term16 A P y).
Proof. exact (MK_COMB (@lem13450) (@lem13451 A P y)). Qed.
Lemma lem13454 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem13455 {A : Type'} (P : A -> Prop) (y : A) : (term16 A P y) = (P y).
Proof. exact (@lem13454 (P y)). Qed.
Lemma lem13456 {A : Type'} (P : A -> Prop) (y : A) : (term26 A P y) = (P y).
Proof. exact (TRANS (@lem13452 A P y) (@lem13455 A P y)). Qed.
Lemma lem13457 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term13 A x P y) = (term27 A P y).
Proof. exact (MK_COMB (@lem13444 A P x) (@lem13456 A P y)). Qed.
Lemma lem13459 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem13460 {A : Type'} (P : A -> Prop) (y : A) : (term27 A P y) = (P y).
Proof. exact (@lem13459 (P y)). Qed.
Lemma lem13461 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term13 A x P y) = (P y).
Proof. exact (TRANS (@lem13457 A x P y) (@lem13460 A P y)). Qed.
Lemma lem13462 {A : Type'} (x : A) (P : A -> Prop) (y : A) : ((term12 A P x y) = (term13 A x P y)) = ((P y) = (P y)).
Proof. exact (MK_COMB (@lem13437 A x P y) (@lem13461 A x P y)). Qed.
Lemma lem13464 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13465 (x : Prop) : (x = x) = True.
Proof. exact (@lem13464 Prop x). Qed.
Lemma lem13466 {A : Type'} (P : A -> Prop) (y : A) : ((P y) = (P y)) = True.
Proof. exact (@lem13465 (P y)). Qed.
Lemma lem13467 {A : Type'} (x : A) (P : A -> Prop) (y : A) : ((term12 A P x y) = (term13 A x P y)) = True.
Proof. exact (TRANS (@lem13462 A x P y) (@lem13466 A P y)). Qed.
Lemma lem13468 {A : Type'} (x : A) (P : A -> Prop) (y : A) : True = ((term12 A P x y) = (term13 A x P y)).
Proof. exact (SYM (@lem13467 A x P y)). Qed.
Lemma lem13469 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term12 A P x y) = (term13 A x P y).
Proof. exact (EQ_MP (@lem13468 A x P y) (@lem0)). Qed.
Lemma lem13470 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = False) : (term8 A P c x y) = (term9 A x c P y).
Proof. exact (EQ_MP (@lem13385 A x P y c h1) (@lem13469 A x P y)). Qed.
Lemma lem13471 {A : Type'} (x : A) (P : A -> Prop) (y : A) (c : Prop) (h1 : c = True) : (term8 A P c x y) = (term9 A x c P y).
Proof. exact (EQ_MP (@lem13372 A x P y c h1) (@lem13427 A x P y)). Qed.
Lemma lem13472 {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A) : (term8 A P c x y) = (term9 A x c P y).
Proof. exact (or_elim (@lem13357 c) (fun h0 : c = True => @lem13471 A x P y c h0) (fun h0 : c = False => @lem13470 A x P y c h0)). Qed.
