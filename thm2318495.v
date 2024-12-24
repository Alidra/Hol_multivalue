Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318495_term_abbrevs.
Require Import INT_LT_DISCRETE_spec.
Require Import INT_NOT_EQ_spec.
Require Import INT_NOT_LE_spec.
Require Import INT_NOT_LT_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2318372 (x : int) : term0 x.
Proof. exact (@lem2299447 x). Qed.
Lemma lem2318373 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318374 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318373 x) (@lem2318372 x)). Qed.
Lemma lem2318375 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318374 x y). Qed.
Lemma lem2318376 (x : int) (y : int) : (term2 x y) = ((int_lt x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2318378 (x : int) : term4 x.
Proof. exact (@lem2306747 x). Qed.
Lemma lem2318379 (x : int) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2318380 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2318379 x) (@lem2318378 x)). Qed.
Lemma lem2318381 (x : int) (y : int) : term6 x y.
Proof. exact (@lem2318380 x y). Qed.
Lemma lem2318382 (y : int) (x : int) : (term6 x y) = ((term7 x y) = (term8 y x)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem2318384 (x : int) : term9 x.
Proof. exact (@lem2306785 x). Qed.
Lemma lem2318385 (x : int) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2318386 (x : int) : term10 x.
Proof. exact (EQ_MP (@lem2318385 x) (@lem2318384 x)). Qed.
Lemma lem2318387 (x : int) (y : int) : term11 x y.
Proof. exact (@lem2318386 x y). Qed.
Lemma lem2318388 (y : int) (x : int) : (term11 x y) = ((term12 x y) = (int_le y x)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2318390 (x : int) : term13 x.
Proof. exact (@lem2306766 x). Qed.
Lemma lem2318391 (x : int) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2318392 (x : int) : term14 x.
Proof. exact (EQ_MP (@lem2318391 x) (@lem2318390 x)). Qed.
Lemma lem2318393 (x : int) (y : int) : term15 x y.
Proof. exact (@lem2318392 x y). Qed.
Lemma lem2318394 (y : int) (x : int) : (term15 x y) = ((term16 x y) = (int_lt y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem2318401 (y : int) (x : int) : (term16 x y) = (int_lt y x).
Proof. exact (EQ_MP (@lem2318394 y x) (@lem2318393 x y)). Qed.
Lemma lem2318403 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2318376 x y) (@lem2318375 x y)). Qed.
Lemma lem2318404 (y : int) (x : int) : (int_lt y x) = (term3 y x).
Proof. exact (@lem2318403 y x). Qed.
Lemma lem2318405 (y : int) (x : int) : (term16 x y) = (term3 y x).
Proof. exact (TRANS (@lem2318401 y x) (@lem2318404 y x)). Qed.
Lemma lem2318406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318407 (y : int) (x : int) : (term17 x y) = (term18 y x).
Proof. exact (MK_COMB (@lem2318406) (@lem2318405 y x)). Qed.
Lemma lem2318408 (y : int) (x : int) : (term3 y x) = (term3 y x).
Proof. exact (eq_refl (term3 y x)). Qed.
Lemma lem2318409 (y : int) (x : int) : ((term16 x y) = (term3 y x)) = ((term3 y x) = (term3 y x)).
Proof. exact (MK_COMB (@lem2318407 y x) (@lem2318408 y x)). Qed.
Lemma lem2318411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318412 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318411 Prop x). Qed.
Lemma lem2318413 (y : int) (x : int) : ((term3 y x) = (term3 y x)) = True.
Proof. exact (@lem2318412 (term3 y x)). Qed.
Lemma lem2318414 (y : int) (x : int) : ((term16 x y) = (term3 y x)) = True.
Proof. exact (TRANS (@lem2318409 y x) (@lem2318413 y x)). Qed.
Lemma lem2318415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2318416 (y : int) (x : int) : (term19 y x) = (and True).
Proof. exact (MK_COMB (@lem2318415) (@lem2318414 y x)). Qed.
Lemma lem2318422 (y : int) (x : int) : (term12 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem2318388 y x) (@lem2318387 x y)). Qed.
Lemma lem2318423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318424 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (MK_COMB (@lem2318423) (@lem2318422 y x)). Qed.
Lemma lem2318425 (y : int) (x : int) : (int_le y x) = (int_le y x).
Proof. exact (eq_refl (int_le y x)). Qed.
Lemma lem2318426 (y : int) (x : int) : ((term12 x y) = (int_le y x)) = ((int_le y x) = (int_le y x)).
Proof. exact (MK_COMB (@lem2318424 y x) (@lem2318425 y x)). Qed.
Lemma lem2318428 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318429 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318428 Prop x). Qed.
Lemma lem2318430 (y : int) (x : int) : ((int_le y x) = (int_le y x)) = True.
Proof. exact (@lem2318429 (int_le y x)). Qed.
Lemma lem2318431 (y : int) (x : int) : ((term12 x y) = (int_le y x)) = True.
Proof. exact (TRANS (@lem2318426 y x) (@lem2318430 y x)). Qed.
Lemma lem2318432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2318433 (y : int) (x : int) : (term22 y x) = (and True).
Proof. exact (MK_COMB (@lem2318432) (@lem2318431 y x)). Qed.
Lemma lem2318439 (y : int) (x : int) : (term7 x y) = (term8 y x).
Proof. exact (EQ_MP (@lem2318382 y x) (@lem2318381 x y)). Qed.
Lemma lem2318443 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2318376 x y) (@lem2318375 x y)). Qed.
Lemma lem2318444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318445 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem2318444) (@lem2318443 x y)). Qed.
Lemma lem2318447 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2318376 x y) (@lem2318375 x y)). Qed.
Lemma lem2318448 (y : int) (x : int) : (int_lt y x) = (term3 y x).
Proof. exact (@lem2318447 y x). Qed.
Lemma lem2318449 (y : int) (x : int) : (term8 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem2318445 x y) (@lem2318448 y x)). Qed.
Lemma lem2318452 (y : int) (x : int) : (term7 x y) = (term25 y x).
Proof. exact (TRANS (@lem2318439 y x) (@lem2318449 y x)). Qed.
Lemma lem2318453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318454 (y : int) (x : int) : (term26 x y) = (term27 y x).
Proof. exact (MK_COMB (@lem2318453) (@lem2318452 y x)). Qed.
Lemma lem2318457 (y : int) (x : int) : (term25 y x) = (term25 y x).
Proof. exact (eq_refl (term25 y x)). Qed.
Lemma lem2318458 (y : int) (x : int) : ((term7 x y) = (term25 y x)) = ((term25 y x) = (term25 y x)).
Proof. exact (MK_COMB (@lem2318454 y x) (@lem2318457 y x)). Qed.
Lemma lem2318460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318461 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318460 Prop x). Qed.
Lemma lem2318462 (y : int) (x : int) : ((term25 y x) = (term25 y x)) = True.
Proof. exact (@lem2318461 (term25 y x)). Qed.
Lemma lem2318463 (y : int) (x : int) : ((term7 x y) = (term25 y x)) = True.
Proof. exact (TRANS (@lem2318458 y x) (@lem2318462 y x)). Qed.
Lemma lem2318464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2318465 (y : int) (x : int) : (term28 y x) = (and True).
Proof. exact (MK_COMB (@lem2318464) (@lem2318463 y x)). Qed.
Lemma lem2318469 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2318376 x y) (@lem2318375 x y)). Qed.
Lemma lem2318470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318471 (x : int) (y : int) : (term29 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2318470) (@lem2318469 x y)). Qed.
Lemma lem2318472 (x : int) (y : int) : (term3 x y) = (term3 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2318473 (x : int) (y : int) : ((int_lt x y) = (term3 x y)) = ((term3 x y) = (term3 x y)).
Proof. exact (MK_COMB (@lem2318471 x y) (@lem2318472 x y)). Qed.
Lemma lem2318475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318476 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318475 Prop x). Qed.
Lemma lem2318477 (x : int) (y : int) : ((term3 x y) = (term3 x y)) = True.
Proof. exact (@lem2318476 (term3 x y)). Qed.
Lemma lem2318478 (x : int) (y : int) : ((int_lt x y) = (term3 x y)) = True.
Proof. exact (TRANS (@lem2318473 x y) (@lem2318477 x y)). Qed.
Lemma lem2318479 (x : int) (y : int) : (term30 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem2318465 y x) (@lem2318478 x y)). Qed.
Lemma lem2318481 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2318482 : (True /\ True) = True.
Proof. exact (@lem2318481 True). Qed.
Lemma lem2318483 (x : int) (y : int) : (term30 x y) = True.
Proof. exact (TRANS (@lem2318479 x y) (@lem2318482)). Qed.
Lemma lem2318484 (x : int) (y : int) : (term31 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem2318433 y x) (@lem2318483 x y)). Qed.
Lemma lem2318486 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2318487 : (True /\ True) = True.
Proof. exact (@lem2318486 True). Qed.
Lemma lem2318488 (x : int) (y : int) : (term31 x y) = True.
Proof. exact (TRANS (@lem2318484 x y) (@lem2318487)). Qed.
Lemma lem2318489 (x : int) (y : int) : (term32 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem2318416 y x) (@lem2318488 x y)). Qed.
Lemma lem2318491 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2318492 : (True /\ True) = True.
Proof. exact (@lem2318491 True). Qed.
Lemma lem2318493 (x : int) (y : int) : (term32 x y) = True.
Proof. exact (TRANS (@lem2318489 x y) (@lem2318492)). Qed.
Lemma lem2318494 (x : int) (y : int) : True = (term32 x y).
Proof. exact (SYM (@lem2318493 x y)). Qed.
Lemma lem2318495 (x : int) (y : int) : term32 x y.
Proof. exact (EQ_MP (@lem2318494 x y) (@lem0)). Qed.
