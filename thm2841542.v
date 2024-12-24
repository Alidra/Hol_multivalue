Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841542_term_abbrevs.
Require Import INT_LT_DISCRETE_spec.
Require Import INT_NOT_EQ_spec.
Require Import INT_NOT_LE_spec.
Require Import INT_NOT_LT_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2841419 (x : int) : term0 x.
Proof. exact (@lem2299447 x). Qed.
Lemma lem2841420 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2841421 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2841420 x) (@lem2841419 x)). Qed.
Lemma lem2841422 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2841421 x y). Qed.
Lemma lem2841423 (x : int) (y : int) : (term2 x y) = ((int_lt x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2841425 (x : int) : term4 x.
Proof. exact (@lem2306747 x). Qed.
Lemma lem2841426 (x : int) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2841427 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2841426 x) (@lem2841425 x)). Qed.
Lemma lem2841428 (x : int) (y : int) : term6 x y.
Proof. exact (@lem2841427 x y). Qed.
Lemma lem2841429 (y : int) (x : int) : (term6 x y) = ((term7 x y) = (term8 y x)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem2841431 (x : int) : term9 x.
Proof. exact (@lem2306785 x). Qed.
Lemma lem2841432 (x : int) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2841433 (x : int) : term10 x.
Proof. exact (EQ_MP (@lem2841432 x) (@lem2841431 x)). Qed.
Lemma lem2841434 (x : int) (y : int) : term11 x y.
Proof. exact (@lem2841433 x y). Qed.
Lemma lem2841435 (y : int) (x : int) : (term11 x y) = ((term12 x y) = (int_le y x)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2841437 (x : int) : term13 x.
Proof. exact (@lem2306766 x). Qed.
Lemma lem2841438 (x : int) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2841439 (x : int) : term14 x.
Proof. exact (EQ_MP (@lem2841438 x) (@lem2841437 x)). Qed.
Lemma lem2841440 (x : int) (y : int) : term15 x y.
Proof. exact (@lem2841439 x y). Qed.
Lemma lem2841441 (y : int) (x : int) : (term15 x y) = ((term16 x y) = (int_lt y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem2841448 (y : int) (x : int) : (term16 x y) = (int_lt y x).
Proof. exact (EQ_MP (@lem2841441 y x) (@lem2841440 x y)). Qed.
Lemma lem2841450 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2841423 x y) (@lem2841422 x y)). Qed.
Lemma lem2841451 (y : int) (x : int) : (int_lt y x) = (term3 y x).
Proof. exact (@lem2841450 y x). Qed.
Lemma lem2841452 (y : int) (x : int) : (term16 x y) = (term3 y x).
Proof. exact (TRANS (@lem2841448 y x) (@lem2841451 y x)). Qed.
Lemma lem2841453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2841454 (y : int) (x : int) : (term17 x y) = (term18 y x).
Proof. exact (MK_COMB (@lem2841453) (@lem2841452 y x)). Qed.
Lemma lem2841455 (y : int) (x : int) : (term3 y x) = (term3 y x).
Proof. exact (eq_refl (term3 y x)). Qed.
Lemma lem2841456 (y : int) (x : int) : ((term16 x y) = (term3 y x)) = ((term3 y x) = (term3 y x)).
Proof. exact (MK_COMB (@lem2841454 y x) (@lem2841455 y x)). Qed.
Lemma lem2841458 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2841459 (x : Prop) : (x = x) = True.
Proof. exact (@lem2841458 Prop x). Qed.
Lemma lem2841460 (y : int) (x : int) : ((term3 y x) = (term3 y x)) = True.
Proof. exact (@lem2841459 (term3 y x)). Qed.
Lemma lem2841461 (y : int) (x : int) : ((term16 x y) = (term3 y x)) = True.
Proof. exact (TRANS (@lem2841456 y x) (@lem2841460 y x)). Qed.
Lemma lem2841462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2841463 (y : int) (x : int) : (term19 y x) = (and True).
Proof. exact (MK_COMB (@lem2841462) (@lem2841461 y x)). Qed.
Lemma lem2841469 (y : int) (x : int) : (term12 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem2841435 y x) (@lem2841434 x y)). Qed.
Lemma lem2841470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2841471 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (MK_COMB (@lem2841470) (@lem2841469 y x)). Qed.
Lemma lem2841472 (y : int) (x : int) : (int_le y x) = (int_le y x).
Proof. exact (eq_refl (int_le y x)). Qed.
Lemma lem2841473 (y : int) (x : int) : ((term12 x y) = (int_le y x)) = ((int_le y x) = (int_le y x)).
Proof. exact (MK_COMB (@lem2841471 y x) (@lem2841472 y x)). Qed.
Lemma lem2841475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2841476 (x : Prop) : (x = x) = True.
Proof. exact (@lem2841475 Prop x). Qed.
Lemma lem2841477 (y : int) (x : int) : ((int_le y x) = (int_le y x)) = True.
Proof. exact (@lem2841476 (int_le y x)). Qed.
Lemma lem2841478 (y : int) (x : int) : ((term12 x y) = (int_le y x)) = True.
Proof. exact (TRANS (@lem2841473 y x) (@lem2841477 y x)). Qed.
Lemma lem2841479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2841480 (y : int) (x : int) : (term22 y x) = (and True).
Proof. exact (MK_COMB (@lem2841479) (@lem2841478 y x)). Qed.
Lemma lem2841486 (y : int) (x : int) : (term7 x y) = (term8 y x).
Proof. exact (EQ_MP (@lem2841429 y x) (@lem2841428 x y)). Qed.
Lemma lem2841490 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2841423 x y) (@lem2841422 x y)). Qed.
Lemma lem2841491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2841492 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem2841491) (@lem2841490 x y)). Qed.
Lemma lem2841494 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2841423 x y) (@lem2841422 x y)). Qed.
Lemma lem2841495 (y : int) (x : int) : (int_lt y x) = (term3 y x).
Proof. exact (@lem2841494 y x). Qed.
Lemma lem2841496 (y : int) (x : int) : (term8 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem2841492 x y) (@lem2841495 y x)). Qed.
Lemma lem2841499 (y : int) (x : int) : (term7 x y) = (term25 y x).
Proof. exact (TRANS (@lem2841486 y x) (@lem2841496 y x)). Qed.
Lemma lem2841500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2841501 (y : int) (x : int) : (term26 x y) = (term27 y x).
Proof. exact (MK_COMB (@lem2841500) (@lem2841499 y x)). Qed.
Lemma lem2841504 (y : int) (x : int) : (term25 y x) = (term25 y x).
Proof. exact (eq_refl (term25 y x)). Qed.
Lemma lem2841505 (y : int) (x : int) : ((term7 x y) = (term25 y x)) = ((term25 y x) = (term25 y x)).
Proof. exact (MK_COMB (@lem2841501 y x) (@lem2841504 y x)). Qed.
Lemma lem2841507 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2841508 (x : Prop) : (x = x) = True.
Proof. exact (@lem2841507 Prop x). Qed.
Lemma lem2841509 (y : int) (x : int) : ((term25 y x) = (term25 y x)) = True.
Proof. exact (@lem2841508 (term25 y x)). Qed.
Lemma lem2841510 (y : int) (x : int) : ((term7 x y) = (term25 y x)) = True.
Proof. exact (TRANS (@lem2841505 y x) (@lem2841509 y x)). Qed.
Lemma lem2841511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2841512 (y : int) (x : int) : (term28 y x) = (and True).
Proof. exact (MK_COMB (@lem2841511) (@lem2841510 y x)). Qed.
Lemma lem2841516 (x : int) (y : int) : (int_lt x y) = (term3 x y).
Proof. exact (EQ_MP (@lem2841423 x y) (@lem2841422 x y)). Qed.
Lemma lem2841517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2841518 (x : int) (y : int) : (term29 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2841517) (@lem2841516 x y)). Qed.
Lemma lem2841519 (x : int) (y : int) : (term3 x y) = (term3 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2841520 (x : int) (y : int) : ((int_lt x y) = (term3 x y)) = ((term3 x y) = (term3 x y)).
Proof. exact (MK_COMB (@lem2841518 x y) (@lem2841519 x y)). Qed.
Lemma lem2841522 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2841523 (x : Prop) : (x = x) = True.
Proof. exact (@lem2841522 Prop x). Qed.
Lemma lem2841524 (x : int) (y : int) : ((term3 x y) = (term3 x y)) = True.
Proof. exact (@lem2841523 (term3 x y)). Qed.
Lemma lem2841525 (x : int) (y : int) : ((int_lt x y) = (term3 x y)) = True.
Proof. exact (TRANS (@lem2841520 x y) (@lem2841524 x y)). Qed.
Lemma lem2841526 (x : int) (y : int) : (term30 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem2841512 y x) (@lem2841525 x y)). Qed.
Lemma lem2841528 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2841529 : (True /\ True) = True.
Proof. exact (@lem2841528 True). Qed.
Lemma lem2841530 (x : int) (y : int) : (term30 x y) = True.
Proof. exact (TRANS (@lem2841526 x y) (@lem2841529)). Qed.
Lemma lem2841531 (x : int) (y : int) : (term31 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem2841480 y x) (@lem2841530 x y)). Qed.
Lemma lem2841533 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2841534 : (True /\ True) = True.
Proof. exact (@lem2841533 True). Qed.
Lemma lem2841535 (x : int) (y : int) : (term31 x y) = True.
Proof. exact (TRANS (@lem2841531 x y) (@lem2841534)). Qed.
Lemma lem2841536 (x : int) (y : int) : (term32 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem2841463 y x) (@lem2841535 x y)). Qed.
Lemma lem2841538 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2841539 : (True /\ True) = True.
Proof. exact (@lem2841538 True). Qed.
Lemma lem2841540 (x : int) (y : int) : (term32 x y) = True.
Proof. exact (TRANS (@lem2841536 x y) (@lem2841539)). Qed.
Lemma lem2841541 (x : int) (y : int) : True = (term32 x y).
Proof. exact (SYM (@lem2841540 x y)). Qed.
Lemma lem2841542 (x : int) (y : int) : term32 x y.
Proof. exact (EQ_MP (@lem2841541 x y) (@lem0)). Qed.
