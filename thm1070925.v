Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070925_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7129_spec.
Require Import thm7400_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem1070452 {A : Type'} (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : a = NIL'.
Proof. exact (h1). Qed.
Lemma lem1070453 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (h1 : list' NIL') : list' NIL'.
Proof. exact (h1). Qed.
Lemma lem1070454 {A : Type'} (list' : type1338 A) : list' = list'.
Proof. exact (eq_refl list'). Qed.
Lemma lem1070455 {A : Type'} (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : (list' a) = (list' NIL').
Proof. exact (MK_COMB (@lem1070454 A list') (@lem1070452 A a NIL' h1)). Qed.
Lemma lem1070456 {A : Type'} (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : (list' NIL') = (list' a).
Proof. exact (SYM (@lem1070455 A list' a NIL' h1)). Qed.
Lemma lem1070457 {A : Type'} (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : list' NIL') (h2 : a = NIL') : list' a.
Proof. exact (EQ_MP (@lem1070456 A list' a NIL' h2) (@lem1070453 A list' NIL' h1)). Qed.
Lemma lem1070458 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (h1 : list' NIL') : term0 A NIL' list' a.
Proof. exact (fun h0 : a = NIL' => @lem1070457 A list' a NIL' h1 h0). Qed.
Lemma lem1070459 {A : Type'} (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : a = NIL'.
Proof. exact (h1). Qed.
Lemma lem1070460 {A : Type'} (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : list' NIL') (h2 : a = NIL') : list' a.
Proof. exact (@lem1070458 A a list' NIL' h1 (@lem1070459 A a NIL' h2)). Qed.
Lemma lem1070461 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (h1 : list' NIL') : term0 A NIL' list' a.
Proof. exact (fun h0 : a = NIL' => @lem1070460 A list' a NIL' h1 h0). Qed.
Lemma lem1070462 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (h1 : list' NIL') : term1 A NIL' list'.
Proof. exact (fun a : recspace A => @lem1070461 A a list' NIL' h1). Qed.
Lemma lem1070463 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (h1 : term1 A NIL' list') : term1 A NIL' list'.
Proof. exact (h1). Qed.
Lemma lem1070464 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (h1 : term1 A NIL' list') : term2 A list' NIL'.
Proof. exact (@lem1070463 A NIL' list' h1 NIL'). Qed.
Lemma lem1070465 {A : Type'} (list' : type1338 A) (NIL' : recspace A) : (term2 A list' NIL') = (term3 A list' NIL').
Proof. exact (eq_refl (term2 A list' NIL')). Qed.
Lemma lem1070466 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (h1 : term1 A NIL' list') : term3 A list' NIL'.
Proof. exact (EQ_MP (@lem1070465 A list' NIL') (@lem1070464 A NIL' list' h1)). Qed.
Lemma lem1070467 {A : Type'} (NIL' : recspace A) : NIL' = NIL'.
Proof. exact (eq_refl NIL'). Qed.
Lemma lem1070468 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (h1 : term1 A NIL' list') : list' NIL'.
Proof. exact (@lem1070466 A NIL' list' h1 (@lem1070467 A NIL')). Qed.
Lemma lem1070469 {A : Type'} (list' : type1338 A) (NIL' : recspace A) : term4 A list' NIL'.
Proof. exact (fun h0 : term1 A NIL' list' => @lem1070468 A NIL' list' h0). Qed.
Lemma lem1070470 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : term5 A NIL' list'.
Proof. exact (fun h0 : list' NIL' => @lem1070462 A list' NIL' h0). Qed.
Lemma lem1070471 {A : Type'} (list' : type1338 A) (NIL' : recspace A) : term6 A list' NIL'.
Proof. exact (conj (@lem1070470 A NIL' list') (@lem1070469 A list' NIL')). Qed.
Lemma lem1070472 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : (term6 A list' NIL') = ((list' NIL') = (term1 A NIL' list')).
Proof. exact (@lem32 (list' NIL') (term1 A NIL' list')). Qed.
Lemma lem1070473 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : (list' NIL') = (term1 A NIL' list').
Proof. exact (EQ_MP (@lem1070472 A NIL' list') (@lem1070471 A list' NIL')). Qed.
Lemma lem1070474 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : term0 A NIL' list' a) : term0 A NIL' list' a.
Proof. exact (h1). Qed.
Lemma lem1070475 {A : Type'} (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : a = NIL'.
Proof. exact (h1). Qed.
Lemma lem1070476 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : a = NIL') (h2 : term0 A NIL' list' a) : list' a.
Proof. exact (@lem1070474 A NIL' list' a h2 (@lem1070475 A a NIL' h1)). Qed.
Lemma lem1070477 {A : Type'} (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : term7 A NIL' list' a.
Proof. exact (fun h0 : term0 A NIL' list' a => @lem1070476 A NIL' list' a h1 h0). Qed.
Lemma lem1070478 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : term0 A NIL' list' a) : term0 A NIL' list' a.
Proof. exact (h1). Qed.
Lemma lem1070479 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : a = NIL') (h2 : term0 A NIL' list' a) : list' a.
Proof. exact (@lem1070477 A list' a NIL' h1 (@lem1070478 A NIL' list' a h2)). Qed.
Lemma lem1070480 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : term0 A NIL' list' a) : term0 A NIL' list' a.
Proof. exact (fun h0 : a = NIL' => @lem1070479 A NIL' list' a h0 h1). Qed.
Lemma lem1070481 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : term0 A NIL' list' a) : term0 A NIL' list' a.
Proof. exact (h1). Qed.
Lemma lem1070482 {A : Type'} (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : a = NIL'.
Proof. exact (h1). Qed.
Lemma lem1070483 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : a = NIL') (h2 : term0 A NIL' list' a) : list' a.
Proof. exact (@lem1070481 A NIL' list' a h2 (@lem1070482 A a NIL' h1)). Qed.
Lemma lem1070484 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) (h1 : term0 A NIL' list' a) : term0 A NIL' list' a.
Proof. exact (fun h0 : a = NIL' => @lem1070483 A NIL' list' a h0 h1). Qed.
Lemma lem1070485 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) : term8 A NIL' list' a.
Proof. exact (fun h0 : term0 A NIL' list' a => @lem1070484 A NIL' list' a h0). Qed.
Lemma lem1070486 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) : term8 A NIL' list' a.
Proof. exact (fun h0 : term0 A NIL' list' a => @lem1070480 A NIL' list' a h0). Qed.
Lemma lem1070487 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) : term9 A NIL' list' a.
Proof. exact (conj (@lem1070486 A NIL' list' a) (@lem1070485 A NIL' list' a)). Qed.
Lemma lem1070488 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) : (term9 A NIL' list' a) = ((term0 A NIL' list' a) = (term0 A NIL' list' a)).
Proof. exact (@lem32 (term0 A NIL' list' a) (term0 A NIL' list' a)). Qed.
Lemma lem1070489 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) : (term0 A NIL' list' a) = (term0 A NIL' list' a).
Proof. exact (EQ_MP (@lem1070488 A NIL' list' a) (@lem1070487 A NIL' list' a)). Qed.
Lemma lem1070490 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : (term10 A NIL' list') = (term10 A NIL' list').
Proof. exact (fun_ext (fun a : recspace A => @lem1070489 A NIL' list' a)). Qed.
Lemma lem1070491 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1070492 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : (term1 A NIL' list') = (term1 A NIL' list').
Proof. exact (MK_COMB (@lem1070491 A) (@lem1070490 A NIL' list')). Qed.
Lemma lem1070493 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : (list' NIL') = (term1 A NIL' list').
Proof. exact (TRANS (@lem1070473 A NIL' list') (@lem1070492 A NIL' list')). Qed.
Lemma lem1070494 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term11 A a CONS' a0 list' a1.
Proof. exact (h1). Qed.
Lemma lem1070495 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : list' a1.
Proof. exact (proj2 (@lem1070494 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070496 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : a = (CONS' a0 a1).
Proof. exact (proj1 (@lem1070494 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070497 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term12 A list' CONS'.
Proof. exact (h1). Qed.
Lemma lem1070498 {A : Type'} (a0 : A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term13 A list' CONS' a0.
Proof. exact (@lem1070497 A list' CONS' h1 a0). Qed.
Lemma lem1070499 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) : (term13 A list' CONS' a0) = (term14 A list' CONS' a0).
Proof. exact (eq_refl (term13 A list' CONS' a0)). Qed.
Lemma lem1070500 {A : Type'} (a0 : A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term14 A list' CONS' a0.
Proof. exact (EQ_MP (@lem1070499 A list' CONS' a0) (@lem1070498 A a0 list' CONS' h1)). Qed.
Lemma lem1070501 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term15 A list' CONS' a0 a1.
Proof. exact (@lem1070500 A a0 list' CONS' h1 a1). Qed.
Lemma lem1070502 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term15 A list' CONS' a0 a1) = (term16 A list' CONS' a0 a1).
Proof. exact (eq_refl (term15 A list' CONS' a0 a1)). Qed.
Lemma lem1070503 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term16 A list' CONS' a0 a1.
Proof. exact (EQ_MP (@lem1070502 A list' CONS' a0 a1) (@lem1070501 A a0 a1 list' CONS' h1)). Qed.
Lemma lem1070504 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term12 A list' CONS') (h2 : term11 A a CONS' a0 list' a1) : term17 A list' CONS' a0 a1.
Proof. exact (@lem1070503 A a0 a1 list' CONS' h1 (@lem1070495 A a CONS' a0 list' a1 h2)). Qed.
Lemma lem1070505 {A : Type'} (list' : type1338 A) : list' = list'.
Proof. exact (eq_refl list'). Qed.
Lemma lem1070506 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : (list' a) = (term17 A list' CONS' a0 a1).
Proof. exact (MK_COMB (@lem1070505 A list') (@lem1070496 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070507 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : (term17 A list' CONS' a0 a1) = (list' a).
Proof. exact (SYM (@lem1070506 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070508 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term12 A list' CONS') (h2 : term11 A a CONS' a0 list' a1) : list' a.
Proof. exact (EQ_MP (@lem1070507 A a CONS' a0 list' a1 h2) (@lem1070504 A a CONS' a0 list' a1 h1 h2)). Qed.
Lemma lem1070509 {A : Type'} (a0 : A) (a1 : recspace A) (a : recspace A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term18 A CONS' a0 a1 list' a.
Proof. exact (fun h0 : term11 A a CONS' a0 list' a1 => @lem1070508 A a CONS' a0 list' a1 h1 h0). Qed.
Lemma lem1070510 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term11 A a CONS' a0 list' a1.
Proof. exact (h1). Qed.
Lemma lem1070511 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term12 A list' CONS') (h2 : term11 A a CONS' a0 list' a1) : list' a.
Proof. exact (@lem1070509 A a0 a1 a list' CONS' h1 (@lem1070510 A a CONS' a0 list' a1 h2)). Qed.
Lemma lem1070512 {A : Type'} (a0 : A) (a1 : recspace A) (a : recspace A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term18 A CONS' a0 a1 list' a.
Proof. exact (fun h0 : term11 A a CONS' a0 list' a1 => @lem1070511 A a CONS' a0 list' a1 h1 h0). Qed.
Lemma lem1070513 {A : Type'} (a0 : A) (a : recspace A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term19 A CONS' a0 list' a.
Proof. exact (fun a1 : recspace A => @lem1070512 A a0 a1 a list' CONS' h1). Qed.
Lemma lem1070514 {A : Type'} (a : recspace A) (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term20 A CONS' list' a.
Proof. exact (fun a0 : A => @lem1070513 A a0 a list' CONS' h1). Qed.
Lemma lem1070515 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : term12 A list' CONS') : term21 A CONS' list'.
Proof. exact (fun a : recspace A => @lem1070514 A a list' CONS' h1). Qed.
Lemma lem1070516 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term21 A CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070517 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term22 A list' CONS' a0 a1.
Proof. exact (@lem1070516 A CONS' list' h1 (CONS' a0 a1)). Qed.
Lemma lem1070518 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term22 A list' CONS' a0 a1) = (term23 A list' CONS' a0 a1).
Proof. exact (eq_refl (term22 A list' CONS' a0 a1)). Qed.
Lemma lem1070519 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term23 A list' CONS' a0 a1.
Proof. exact (EQ_MP (@lem1070518 A list' CONS' a0 a1) (@lem1070517 A a0 a1 CONS' list' h1)). Qed.
Lemma lem1070520 {A : Type'} (a1 : recspace A) (a0 : A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term24 A list' CONS' a1 a0.
Proof. exact (@lem1070519 A a0 a1 CONS' list' h1 a0). Qed.
Lemma lem1070521 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term24 A list' CONS' a1 a0) = (term25 A list' CONS' a0 a1).
Proof. exact (eq_refl (term24 A list' CONS' a1 a0)). Qed.
Lemma lem1070522 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term25 A list' CONS' a0 a1.
Proof. exact (EQ_MP (@lem1070521 A list' CONS' a0 a1) (@lem1070520 A a1 a0 CONS' list' h1)). Qed.
Lemma lem1070523 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term26 A list' CONS' a0 a1.
Proof. exact (@lem1070522 A a0 a1 CONS' list' h1 a1). Qed.
Lemma lem1070524 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term26 A list' CONS' a0 a1) = (term27 A list' CONS' a0 a1).
Proof. exact (eq_refl (term26 A list' CONS' a0 a1)). Qed.
Lemma lem1070525 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term27 A list' CONS' a0 a1.
Proof. exact (EQ_MP (@lem1070524 A list' CONS' a0 a1) (@lem1070523 A a0 a1 CONS' list' h1)). Qed.
Lemma lem1070526 {A : Type'} (list' : type1338 A) (a1 : recspace A) (h1 : list' a1) : list' a1.
Proof. exact (h1). Qed.
Lemma lem1070527 {A : Type'} (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (CONS' a0 a1) = (CONS' a0 a1).
Proof. exact (eq_refl (CONS' a0 a1)). Qed.
Lemma lem1070528 {A : Type'} (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : list' a1) : term28 A CONS' a0 list' a1.
Proof. exact (conj (@lem1070527 A CONS' a0 a1) (@lem1070526 A list' a1 h1)). Qed.
Lemma lem1070529 {A : Type'} (a0 : A) (CONS' : type1399 A) (list' : type1338 A) (a1 : recspace A) (h1 : term21 A CONS' list') (h2 : list' a1) : term17 A list' CONS' a0 a1.
Proof. exact (@lem1070525 A a0 a1 CONS' list' h1 (@lem1070528 A CONS' a0 list' a1 h2)). Qed.
Lemma lem1070530 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term16 A list' CONS' a0 a1.
Proof. exact (fun h0 : list' a1 => @lem1070529 A a0 CONS' list' a1 h1 h0). Qed.
Lemma lem1070531 {A : Type'} (a0 : A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term14 A list' CONS' a0.
Proof. exact (fun a1 : recspace A => @lem1070530 A a0 a1 CONS' list' h1). Qed.
Lemma lem1070532 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (h1 : term21 A CONS' list') : term12 A list' CONS'.
Proof. exact (fun a0 : A => @lem1070531 A a0 CONS' list' h1). Qed.
Lemma lem1070533 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) : term29 A list' CONS'.
Proof. exact (fun h0 : term21 A CONS' list' => @lem1070532 A CONS' list' h0). Qed.
Lemma lem1070534 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) : term30 A CONS' list'.
Proof. exact (fun h0 : term12 A list' CONS' => @lem1070515 A list' CONS' h0). Qed.
Lemma lem1070535 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) : term31 A list' CONS'.
Proof. exact (conj (@lem1070534 A CONS' list') (@lem1070533 A list' CONS')). Qed.
Lemma lem1070536 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) : (term31 A list' CONS') = ((term12 A list' CONS') = (term21 A CONS' list')).
Proof. exact (@lem32 (term12 A list' CONS') (term21 A CONS' list')). Qed.
Lemma lem1070537 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) : (term12 A list' CONS') = (term21 A CONS' list').
Proof. exact (EQ_MP (@lem1070536 A CONS' list') (@lem1070535 A list' CONS')). Qed.
Lemma lem1070538 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term20 A CONS' list' a.
Proof. exact (h1). Qed.
Lemma lem1070539 {A : Type'} (a0 : A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term32 A CONS' list' a a0.
Proof. exact (@lem1070538 A CONS' list' a h1 a0). Qed.
Lemma lem1070540 {A : Type'} (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a : recspace A) : (term32 A CONS' list' a a0) = (term19 A CONS' a0 list' a).
Proof. exact (eq_refl (term32 A CONS' list' a a0)). Qed.
Lemma lem1070541 {A : Type'} (a0 : A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term19 A CONS' a0 list' a.
Proof. exact (EQ_MP (@lem1070540 A CONS' a0 list' a) (@lem1070539 A a0 CONS' list' a h1)). Qed.
Lemma lem1070542 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term33 A CONS' a0 list' a a1.
Proof. exact (@lem1070541 A a0 CONS' list' a h1 a1). Qed.
Lemma lem1070543 {A : Type'} (CONS' : type1399 A) (a0 : A) (a1 : recspace A) (list' : type1338 A) (a : recspace A) : (term33 A CONS' a0 list' a a1) = (term18 A CONS' a0 a1 list' a).
Proof. exact (eq_refl (term33 A CONS' a0 list' a a1)). Qed.
Lemma lem1070544 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term18 A CONS' a0 a1 list' a.
Proof. exact (EQ_MP (@lem1070543 A CONS' a0 a1 list' a) (@lem1070542 A a0 a1 CONS' list' a h1)). Qed.
Lemma lem1070545 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term11 A a CONS' a0 list' a1.
Proof. exact (h1). Qed.
Lemma lem1070546 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term20 A CONS' list' a) (h2 : term11 A a CONS' a0 list' a1) : list' a.
Proof. exact (@lem1070544 A a0 a1 CONS' list' a h1 (@lem1070545 A a CONS' a0 list' a1 h2)). Qed.
Lemma lem1070547 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term34 A CONS' list' a.
Proof. exact (fun h0 : term20 A CONS' list' a => @lem1070546 A a CONS' a0 list' a1 h0 h1). Qed.
Lemma lem1070548 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (h1 : term35 A a CONS' a0 list') : term35 A a CONS' a0 list'.
Proof. exact (h1). Qed.
Lemma lem1070549 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (h1 : term35 A a CONS' a0 list') : term34 A CONS' list' a.
Proof. exact (ex_elim (@lem1070548 A a CONS' a0 list' h1) (fun a1 : recspace A => fun h0 : term36 A a CONS' a0 list' a1 => @lem1070547 A a CONS' a0 list' a1 h0)). Qed.
Lemma lem1070550 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term37 A a CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070551 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term34 A CONS' list' a.
Proof. exact (ex_elim (@lem1070550 A a CONS' list' h1) (fun a0 : A => fun h0 : term38 A a CONS' list' a0 => @lem1070549 A a CONS' a0 list' h0)). Qed.
Lemma lem1070552 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term20 A CONS' list' a.
Proof. exact (h1). Qed.
Lemma lem1070553 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term20 A CONS' list' a) (h2 : term37 A a CONS' list') : list' a.
Proof. exact (@lem1070551 A a CONS' list' h2 (@lem1070552 A CONS' list' a h1)). Qed.
Lemma lem1070554 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term20 A CONS' list' a) : term39 A CONS' list' a.
Proof. exact (fun h0 : term37 A a CONS' list' => @lem1070553 A a CONS' list' h1 h0). Qed.
Lemma lem1070555 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term39 A CONS' list' a) : term39 A CONS' list' a.
Proof. exact (h1). Qed.
Lemma lem1070556 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term11 A a CONS' a0 list' a1.
Proof. exact (h1). Qed.
Lemma lem1070557 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term35 A a CONS' a0 list'.
Proof. exact (ex_intro (term36 A a CONS' a0 list') a1 (@lem1070556 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070558 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) (h1 : term11 A a CONS' a0 list' a1) : term37 A a CONS' list'.
Proof. exact (ex_intro (term38 A a CONS' list') a0 (@lem1070557 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070559 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term11 A a CONS' a0 list' a1) (h2 : term39 A CONS' list' a) : list' a.
Proof. exact (@lem1070555 A CONS' list' a h2 (@lem1070558 A a CONS' a0 list' a1 h1)). Qed.
Lemma lem1070560 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term39 A CONS' list' a) : term18 A CONS' a0 a1 list' a.
Proof. exact (fun h0 : term11 A a CONS' a0 list' a1 => @lem1070559 A a0 a1 CONS' list' a h0 h1). Qed.
Lemma lem1070561 {A : Type'} (a0 : A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term39 A CONS' list' a) : term19 A CONS' a0 list' a.
Proof. exact (fun a1 : recspace A => @lem1070560 A a0 a1 CONS' list' a h1). Qed.
Lemma lem1070562 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (h1 : term39 A CONS' list' a) : term20 A CONS' list' a.
Proof. exact (fun a0 : A => @lem1070561 A a0 CONS' list' a h1). Qed.
Lemma lem1070563 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : term40 A CONS' list' a.
Proof. exact (fun h0 : term39 A CONS' list' a => @lem1070562 A CONS' list' a h0). Qed.
Lemma lem1070564 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : term41 A CONS' list' a.
Proof. exact (fun h0 : term20 A CONS' list' a => @lem1070554 A CONS' list' a h0). Qed.
Lemma lem1070565 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : term42 A CONS' list' a.
Proof. exact (conj (@lem1070564 A CONS' list' a) (@lem1070563 A CONS' list' a)). Qed.
Lemma lem1070566 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term42 A CONS' list' a) = ((term20 A CONS' list' a) = (term39 A CONS' list' a)).
Proof. exact (@lem32 (term20 A CONS' list' a) (term39 A CONS' list' a)). Qed.
Lemma lem1070567 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term20 A CONS' list' a) = (term39 A CONS' list' a).
Proof. exact (EQ_MP (@lem1070566 A CONS' list' a) (@lem1070565 A CONS' list' a)). Qed.
Lemma lem1070568 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) : (term43 A CONS' list') = (term44 A CONS' list').
Proof. exact (fun_ext (fun a : recspace A => @lem1070567 A CONS' list' a)). Qed.
Lemma lem1070569 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1070570 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) : (term21 A CONS' list') = (term45 A CONS' list').
Proof. exact (MK_COMB (@lem1070569 A) (@lem1070568 A CONS' list')). Qed.
Lemma lem1070571 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) : (term12 A list' CONS') = (term45 A CONS' list').
Proof. exact (TRANS (@lem1070537 A CONS' list') (@lem1070570 A CONS' list')). Qed.
Lemma lem1070573 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem1070574 (x : Prop) : (x = x) = True.
Proof. exact (@lem1070573 Prop x). Qed.
Lemma lem1070575 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : ((term46 A NIL' CONS' list') = (term46 A NIL' CONS' list')) = True.
Proof. exact (@lem1070574 (term46 A NIL' CONS' list')). Qed.
Lemma lem1070576 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : True = ((term46 A NIL' CONS' list') = (term46 A NIL' CONS' list')).
Proof. exact (SYM (@lem1070575 A NIL' CONS' list')). Qed.
Lemma lem1070577 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term46 A NIL' CONS' list') = (term46 A NIL' CONS' list').
Proof. exact (EQ_MP (@lem1070576 A NIL' CONS' list') (@lem0)). Qed.
Lemma lem1070578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1070579 {A : Type'} (NIL' : recspace A) (list' : type1338 A) : (term47 A list' NIL') = (term48 A NIL' list').
Proof. exact (MK_COMB (@lem1070578) (@lem1070493 A NIL' list')). Qed.
Lemma lem1070580 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term49 A NIL' list' CONS') = (term46 A NIL' CONS' list').
Proof. exact (MK_COMB (@lem1070579 A NIL' list') (@lem1070571 A CONS' list')). Qed.
Lemma lem1070581 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term49 A NIL' list' CONS') = (term46 A NIL' CONS' list').
Proof. exact (TRANS (@lem1070580 A NIL' CONS' list') (@lem1070577 A NIL' CONS' list')). Qed.
Lemma lem1070582 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term46 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070583 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term45 A CONS' list'.
Proof. exact (proj2 (@lem1070582 A NIL' CONS' list' h1)). Qed.
Lemma lem1070584 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term1 A NIL' list'.
Proof. exact (proj1 (@lem1070582 A NIL' CONS' list' h1)). Qed.
Lemma lem1070585 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term50 A NIL' list' a.
Proof. exact (@lem1070584 A NIL' CONS' list' h1 a). Qed.
Lemma lem1070586 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (a : recspace A) : (term50 A NIL' list' a) = (term0 A NIL' list' a).
Proof. exact (eq_refl (term50 A NIL' list' a)). Qed.
Lemma lem1070587 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term0 A NIL' list' a.
Proof. exact (EQ_MP (@lem1070586 A NIL' list' a) (@lem1070585 A a NIL' CONS' list' h1)). Qed.
Lemma lem1070588 {A : Type'} (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : a = NIL'.
Proof. exact (h1). Qed.
Lemma lem1070589 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : term46 A NIL' CONS' list') (h2 : a = NIL') : list' a.
Proof. exact (@lem1070587 A a NIL' CONS' list' h1 (@lem1070588 A a NIL' h2)). Qed.
Lemma lem1070590 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : term51 A NIL' CONS' list' a.
Proof. exact (fun h0 : term46 A NIL' CONS' list' => @lem1070589 A CONS' list' a NIL' h0 h1). Qed.
Lemma lem1070591 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term52 A CONS' list' a.
Proof. exact (@lem1070583 A NIL' CONS' list' h1 a). Qed.
Lemma lem1070592 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term52 A CONS' list' a) = (term39 A CONS' list' a).
Proof. exact (eq_refl (term52 A CONS' list' a)). Qed.
Lemma lem1070593 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term39 A CONS' list' a.
Proof. exact (EQ_MP (@lem1070592 A CONS' list' a) (@lem1070591 A a NIL' CONS' list' h1)). Qed.
Lemma lem1070594 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term37 A a CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070595 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') (h2 : term46 A NIL' CONS' list') : list' a.
Proof. exact (@lem1070593 A a NIL' CONS' list' h2 (@lem1070594 A a CONS' list' h1)). Qed.
Lemma lem1070596 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term51 A NIL' CONS' list' a.
Proof. exact (fun h0 : term46 A NIL' CONS' list' => @lem1070595 A a NIL' CONS' list' h1 h0). Qed.
Lemma lem1070597 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term53 A NIL' a CONS' list') : term53 A NIL' a CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070598 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term53 A NIL' a CONS' list') : term51 A NIL' CONS' list' a.
Proof. exact (or_elim (@lem1070597 A NIL' a CONS' list' h1) (fun h0 : a = NIL' => @lem1070590 A CONS' list' a NIL' h0) (fun h0 : term37 A a CONS' list' => @lem1070596 A NIL' a CONS' list' h0)). Qed.
Lemma lem1070599 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term46 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070600 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') (h2 : term53 A NIL' a CONS' list') : list' a.
Proof. exact (@lem1070598 A NIL' a CONS' list' h2 (@lem1070599 A NIL' CONS' list' h1)). Qed.
Lemma lem1070601 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term54 A NIL' CONS' list' a.
Proof. exact (fun h0 : term53 A NIL' a CONS' list' => @lem1070600 A NIL' a CONS' list' h1 h0). Qed.
Lemma lem1070602 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term46 A NIL' CONS' list') : term55 A NIL' CONS' list'.
Proof. exact (fun a : recspace A => @lem1070601 A a NIL' CONS' list' h1). Qed.
Lemma lem1070603 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term55 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070604 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term56 A NIL' CONS' list' a.
Proof. exact (@lem1070603 A NIL' CONS' list' h1 a). Qed.
Lemma lem1070605 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term56 A NIL' CONS' list' a) = (term54 A NIL' CONS' list' a).
Proof. exact (eq_refl (term56 A NIL' CONS' list' a)). Qed.
Lemma lem1070606 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term54 A NIL' CONS' list' a.
Proof. exact (EQ_MP (@lem1070605 A NIL' CONS' list' a) (@lem1070604 A a NIL' CONS' list' h1)). Qed.
Lemma lem1070607 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term53 A NIL' a CONS' list') : term53 A NIL' a CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070608 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') (h2 : term53 A NIL' a CONS' list') : list' a.
Proof. exact (@lem1070606 A a NIL' CONS' list' h1 (@lem1070607 A NIL' a CONS' list' h2)). Qed.
Lemma lem1070609 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term53 A NIL' a CONS' list') : term57 A NIL' CONS' list' a.
Proof. exact (fun h0 : term55 A NIL' CONS' list' => @lem1070608 A NIL' a CONS' list' h0 h1). Qed.
Lemma lem1070610 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term37 A a CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070611 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term53 A NIL' a CONS' list'.
Proof. exact (or_intro2 (a = NIL') (@lem1070610 A a CONS' list' h1)). Qed.
Lemma lem1070612 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : (term53 A NIL' a CONS' list') = (term57 A NIL' CONS' list' a).
Proof. exact (prop_ext (fun h2 : term53 A NIL' a CONS' list' => @lem1070609 A NIL' a CONS' list' h2) (fun h2 : term57 A NIL' CONS' list' a => @lem1070611 A NIL' a CONS' list' h1)). Qed.
Lemma lem1070613 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term37 A a CONS' list') : term57 A NIL' CONS' list' a.
Proof. exact (EQ_MP (@lem1070612 A NIL' a CONS' list' h1) (@lem1070611 A NIL' a CONS' list' h1)). Qed.
Lemma lem1070614 {A : Type'} (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : a = NIL'.
Proof. exact (h1). Qed.
Lemma lem1070615 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : term53 A NIL' a CONS' list'.
Proof. exact (or_intro1 (@lem1070614 A a NIL' h1) (term37 A a CONS' list')). Qed.
Lemma lem1070616 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : (term53 A NIL' a CONS' list') = (term57 A NIL' CONS' list' a).
Proof. exact (prop_ext (fun h2 : term53 A NIL' a CONS' list' => @lem1070609 A NIL' a CONS' list' h2) (fun h2 : term57 A NIL' CONS' list' a => @lem1070615 A CONS' list' a NIL' h1)). Qed.
Lemma lem1070617 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : a = NIL') : term57 A NIL' CONS' list' a.
Proof. exact (EQ_MP (@lem1070616 A CONS' list' a NIL' h1) (@lem1070615 A CONS' list' a NIL' h1)). Qed.
Lemma lem1070618 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term55 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070619 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') (h2 : term37 A a CONS' list') : list' a.
Proof. exact (@lem1070613 A NIL' a CONS' list' h2 (@lem1070618 A NIL' CONS' list' h1)). Qed.
Lemma lem1070620 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term39 A CONS' list' a.
Proof. exact (fun h0 : term37 A a CONS' list' => @lem1070619 A NIL' a CONS' list' h1 h0). Qed.
Lemma lem1070621 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term45 A CONS' list'.
Proof. exact (fun a : recspace A => @lem1070620 A a NIL' CONS' list' h1). Qed.
Lemma lem1070622 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term55 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070623 {A : Type'} (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) (NIL' : recspace A) (h1 : term55 A NIL' CONS' list') (h2 : a = NIL') : list' a.
Proof. exact (@lem1070617 A CONS' list' a NIL' h2 (@lem1070622 A NIL' CONS' list' h1)). Qed.
Lemma lem1070624 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term0 A NIL' list' a.
Proof. exact (fun h0 : a = NIL' => @lem1070623 A CONS' list' a NIL' h1 h0). Qed.
Lemma lem1070625 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term1 A NIL' list'.
Proof. exact (fun a : recspace A => @lem1070624 A a NIL' CONS' list' h1). Qed.
Lemma lem1070626 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term46 A NIL' CONS' list'.
Proof. exact (conj (@lem1070625 A NIL' CONS' list' h1) (@lem1070621 A NIL' CONS' list' h1)). Qed.
Lemma lem1070627 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : term58 A NIL' CONS' list'.
Proof. exact (fun h0 : term55 A NIL' CONS' list' => @lem1070626 A NIL' CONS' list' h0). Qed.
Lemma lem1070628 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : term59 A NIL' CONS' list'.
Proof. exact (fun h0 : term46 A NIL' CONS' list' => @lem1070602 A NIL' CONS' list' h0). Qed.
Lemma lem1070629 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : term60 A NIL' CONS' list'.
Proof. exact (conj (@lem1070628 A NIL' CONS' list') (@lem1070627 A NIL' CONS' list')). Qed.
Lemma lem1070630 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term60 A NIL' CONS' list') = ((term46 A NIL' CONS' list') = (term55 A NIL' CONS' list')).
Proof. exact (@lem32 (term46 A NIL' CONS' list') (term55 A NIL' CONS' list')). Qed.
Lemma lem1070631 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term46 A NIL' CONS' list') = (term55 A NIL' CONS' list').
Proof. exact (EQ_MP (@lem1070630 A NIL' CONS' list') (@lem1070629 A NIL' CONS' list')). Qed.
Lemma lem1070632 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term49 A NIL' list' CONS') = (term55 A NIL' CONS' list').
Proof. exact (TRANS (@lem1070581 A NIL' CONS' list') (@lem1070631 A NIL' CONS' list')). Qed.
Lemma lem1070633 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (CONS' : type1399 A) : (term55 A NIL' CONS' list') = (term49 A NIL' list' CONS').
Proof. exact (SYM (@lem1070632 A NIL' CONS' list')). Qed.
Lemma lem1070634 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : list' = (term61 A NIL' CONS').
Proof. exact (h1). Qed.
Lemma lem1070635 {A : Type'} (a : recspace A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1070636 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : (list' a) = (term62 A NIL' CONS' a).
Proof. exact (MK_COMB (@lem1070634 A list' NIL' CONS' h1) (@lem1070635 A a)). Qed.
Lemma lem1070637 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (a : recspace A) : (term62 A NIL' CONS' a) = (term63 A NIL' CONS' a).
Proof. exact (eq_refl (term62 A NIL' CONS' a)). Qed.
Lemma lem1070638 {A : Type'} (list' : type1338 A) (a : recspace A) : (term64 A list' a) = (term64 A list' a).
Proof. exact (eq_refl (term64 A list' a)). Qed.
Lemma lem1070639 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (a : recspace A) : ((list' a) = (term62 A NIL' CONS' a)) = ((list' a) = (term63 A NIL' CONS' a)).
Proof. exact (MK_COMB (@lem1070638 A list' a) (@lem1070637 A NIL' CONS' a)). Qed.
Lemma lem1070640 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : (list' a) = (term63 A NIL' CONS' a).
Proof. exact (EQ_MP (@lem1070639 A list' NIL' CONS' a) (@lem1070636 A a list' NIL' CONS' h1)). Qed.
Lemma lem1070641 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term65 A list' NIL' CONS'.
Proof. exact (fun a : recspace A => @lem1070640 A a list' NIL' CONS' h1). Qed.
Lemma lem1070642 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term66 A list' NIL' CONS' a.
Proof. exact (@lem1070641 A list' NIL' CONS' h1 a). Qed.
Lemma lem1070643 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (a : recspace A) : (term66 A list' NIL' CONS' a) = ((list' a) = (term63 A NIL' CONS' a)).
Proof. exact (eq_refl (term66 A list' NIL' CONS' a)). Qed.
Lemma lem1070644 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : (list' a) = (term63 A NIL' CONS' a).
Proof. exact (EQ_MP (@lem1070643 A list' NIL' CONS' a) (@lem1070642 A a list' NIL' CONS' h1)). Qed.
Lemma lem1070647 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (a : recspace A) : term67 A list' NIL' CONS' a.
Proof. exact (@lem37 (list' a) (term63 A NIL' CONS' a)). Qed.
Lemma lem1070648 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term68 A list' NIL' CONS' a.
Proof. exact (@lem1070647 A list' NIL' CONS' a (@lem1070644 A a list' NIL' CONS' h1)). Qed.
Lemma lem1070649 {A : Type'} (list' : type1338 A) (a : recspace A) (h1 : list' a) : list' a.
Proof. exact (h1). Qed.
Lemma lem1070650 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' a) (h2 : list' = (term61 A NIL' CONS')) : term63 A NIL' CONS' a.
Proof. exact (@lem1070648 A a list' NIL' CONS' h2 (@lem1070649 A list' a h1)). Qed.
Lemma lem1070651 {A : Type'} (list' : type1338 A) (a : recspace A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list'' a) (h2 : list'' = (term61 A NIL' CONS')) : term69 A NIL' CONS' a list'.
Proof. exact (@lem1070650 A a list'' NIL' CONS' h1 h2 list'). Qed.
Lemma lem1070652 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term69 A NIL' CONS' a list') = (term57 A NIL' CONS' list' a).
Proof. exact (eq_refl (term69 A NIL' CONS' a list')). Qed.
Lemma lem1070653 {A : Type'} (list' : type1338 A) (a : recspace A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list'' a) (h2 : list'' = (term61 A NIL' CONS')) : term57 A NIL' CONS' list' a.
Proof. exact (EQ_MP (@lem1070652 A NIL' CONS' list' a) (@lem1070651 A list' a list'' NIL' CONS' h1 h2)). Qed.
Lemma lem1070654 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term55 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070655 {A : Type'} (list' : type1338 A) (a : recspace A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term55 A NIL' CONS' list') (h2 : list'' a) (h3 : list'' = (term61 A NIL' CONS')) : list' a.
Proof. exact (@lem1070653 A list' a list'' NIL' CONS' h2 h3 (@lem1070654 A NIL' CONS' list' h1)). Qed.
Lemma lem1070656 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term55 A NIL' CONS' list') (h2 : list'' = (term61 A NIL' CONS')) : term70 A list'' list' a.
Proof. exact (fun h0 : list'' a => @lem1070655 A list' a list'' NIL' CONS' h1 h0 h2). Qed.
Lemma lem1070657 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term55 A NIL' CONS' list') (h2 : list'' = (term61 A NIL' CONS')) : term71 A list'' list'.
Proof. exact (fun a : recspace A => @lem1070656 A a list' list'' NIL' CONS' h1 h2). Qed.
Lemma lem1070658 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list'' = (term61 A NIL' CONS')) : term72 A NIL' CONS' list'' list'.
Proof. exact (fun h0 : term55 A NIL' CONS' list' => @lem1070657 A list' list'' NIL' CONS' h0 h1). Qed.
Lemma lem1070659 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term73 A NIL' CONS' list'.
Proof. exact (fun list'' : type1338 A => @lem1070658 A list'' list' NIL' CONS' h1). Qed.
Lemma lem1070660 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term74 A NIL' CONS'.
Proof. exact (h1). Qed.
Lemma lem1070661 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term55 A NIL' CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070662 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list'' = (term61 A NIL' CONS')) : term75 A NIL' CONS' list'' list'.
Proof. exact (@lem1070659 A list'' NIL' CONS' h1 list'). Qed.
Lemma lem1070663 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) : (term75 A NIL' CONS' list' list'') = (term72 A NIL' CONS' list' list'').
Proof. exact (eq_refl (term75 A NIL' CONS' list' list'')). Qed.
Lemma lem1070664 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list'' = (term61 A NIL' CONS')) : term72 A NIL' CONS' list'' list'.
Proof. exact (EQ_MP (@lem1070663 A NIL' CONS' list'' list') (@lem1070662 A list' list'' NIL' CONS' h1)). Qed.
Lemma lem1070665 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term55 A NIL' CONS' list') (h2 : list'' = (term61 A NIL' CONS')) : term71 A list'' list'.
Proof. exact (@lem1070664 A list' list'' NIL' CONS' h2 (@lem1070661 A NIL' CONS' list' h1)). Qed.
Lemma lem1070666 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term76 A NIL' CONS' list'.
Proof. exact (@lem1070660 A NIL' CONS' h1 list'). Qed.
Lemma lem1070667 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) : (term76 A NIL' CONS' list') = (term77 A list' NIL' CONS').
Proof. exact (eq_refl (term76 A NIL' CONS' list')). Qed.
Lemma lem1070668 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term77 A list' NIL' CONS'.
Proof. exact (EQ_MP (@lem1070667 A list' NIL' CONS') (@lem1070666 A list' NIL' CONS' h1)). Qed.
Lemma lem1070669 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term78 A list' NIL' CONS' list''.
Proof. exact (@lem1070668 A list' NIL' CONS' h1 list''). Qed.
Lemma lem1070670 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term78 A list' NIL' CONS' list'') = (term79 A list' NIL' CONS' list'').
Proof. exact (eq_refl (term78 A list' NIL' CONS' list'')). Qed.
Lemma lem1070671 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term79 A list' NIL' CONS' list''.
Proof. exact (EQ_MP (@lem1070670 A list' NIL' CONS' list'') (@lem1070669 A list' list'' NIL' CONS' h1)). Qed.
Lemma lem1070672 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : term55 A NIL' CONS' list') (h3 : list'' = (term61 A NIL' CONS')) : term80 A list'' NIL' CONS' list'.
Proof. exact (@lem1070671 A list'' list' NIL' CONS' h1 (@lem1070665 A list' list'' NIL' CONS' h2 h3)). Qed.
Lemma lem1070673 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term56 A NIL' CONS' list' a.
Proof. exact (@lem1070661 A NIL' CONS' list' h1 a). Qed.
Lemma lem1070674 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term56 A NIL' CONS' list' a) = (term54 A NIL' CONS' list' a).
Proof. exact (eq_refl (term56 A NIL' CONS' list' a)). Qed.
Lemma lem1070675 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term55 A NIL' CONS' list') : term54 A NIL' CONS' list' a.
Proof. exact (EQ_MP (@lem1070674 A NIL' CONS' list' a) (@lem1070673 A a NIL' CONS' list' h1)). Qed.
Lemma lem1070676 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : term55 A NIL' CONS' list') (h3 : list'' = (term61 A NIL' CONS')) : term81 A list'' NIL' CONS' list' a.
Proof. exact (@lem1070672 A list' list'' NIL' CONS' h1 h2 h3 a). Qed.
Lemma lem1070677 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term81 A list' NIL' CONS' list'' a) = (term82 A list' NIL' a CONS' list'').
Proof. exact (eq_refl (term81 A list' NIL' CONS' list'' a)). Qed.
Lemma lem1070678 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : term55 A NIL' CONS' list') (h3 : list'' = (term61 A NIL' CONS')) : term82 A list'' NIL' a CONS' list'.
Proof. exact (EQ_MP (@lem1070677 A list'' NIL' a CONS' list') (@lem1070676 A a list' list'' NIL' CONS' h1 h2 h3)). Qed.
Lemma lem1070679 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (a : recspace A) : term83 A NIL' CONS' list' list'' a.
Proof. exact (@lem51 (term53 A NIL' a CONS' list'') (term53 A NIL' a CONS' list') (list'' a)). Qed.
Lemma lem1070680 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : term55 A NIL' CONS' list') (h3 : list'' = (term61 A NIL' CONS')) : term84 A NIL' CONS' list'' list' a.
Proof. exact (@lem1070679 A NIL' CONS' list'' list' a (@lem1070678 A a list' list'' NIL' CONS' h1 h2 h3)). Qed.
Lemma lem1070681 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : term55 A NIL' CONS' list') (h3 : list'' = (term61 A NIL' CONS')) : term85 A NIL' CONS' list'' list' a.
Proof. exact (@lem1070680 A a list' list'' NIL' CONS' h1 h2 h3 (@lem1070675 A a NIL' CONS' list' h2)). Qed.
Lemma lem1070682 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term53 A NIL' a CONS' list') : term53 A NIL' a CONS' list'.
Proof. exact (h1). Qed.
Lemma lem1070683 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) (h1 : term74 A NIL' CONS') (h2 : term55 A NIL' CONS' list') (h3 : list'' = (term61 A NIL' CONS')) (h4 : term53 A NIL' a CONS' list'') : list' a.
Proof. exact (@lem1070681 A a list' list'' NIL' CONS' h1 h2 h3 (@lem1070682 A NIL' a CONS' list'' h4)). Qed.
Lemma lem1070684 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) (h1 : term74 A NIL' CONS') (h2 : list'' = (term61 A NIL' CONS')) (h3 : term53 A NIL' a CONS' list'') : term57 A NIL' CONS' list' a.
Proof. exact (fun h0 : term55 A NIL' CONS' list' => @lem1070683 A list' NIL' a CONS' list'' h1 h0 h2 h3). Qed.
Lemma lem1070685 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) (h3 : term53 A NIL' a CONS' list') : term63 A NIL' CONS' a.
Proof. exact (fun list'' : type1338 A => @lem1070684 A list'' NIL' a CONS' list' h1 h2 h3). Qed.
Lemma lem1070686 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term66 A list' NIL' CONS' a.
Proof. exact (@lem1070641 A list' NIL' CONS' h1 a). Qed.
Lemma lem1070687 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (a : recspace A) : (term66 A list' NIL' CONS' a) = ((list' a) = (term63 A NIL' CONS' a)).
Proof. exact (eq_refl (term66 A list' NIL' CONS' a)). Qed.
Lemma lem1070688 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : (list' a) = (term63 A NIL' CONS' a).
Proof. exact (EQ_MP (@lem1070687 A list' NIL' CONS' a) (@lem1070686 A a list' NIL' CONS' h1)). Qed.
Lemma lem1070689 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : (term63 A NIL' CONS' a) = (list' a).
Proof. exact (SYM (@lem1070688 A a list' NIL' CONS' h1)). Qed.
Lemma lem1070690 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) (h3 : term53 A NIL' a CONS' list') : list' a.
Proof. exact (EQ_MP (@lem1070689 A a list' NIL' CONS' h2) (@lem1070685 A NIL' a CONS' list' h1 h2 h3)). Qed.
Lemma lem1070691 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term54 A NIL' CONS' list' a.
Proof. exact (fun h0 : term53 A NIL' a CONS' list' => @lem1070690 A NIL' a CONS' list' h1 h2 h0). Qed.
Lemma lem1070692 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term55 A NIL' CONS' list'.
Proof. exact (fun a : recspace A => @lem1070691 A a list' NIL' CONS' h1 h2). Qed.
Lemma lem1070695 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term86 A NIL' CONS' list' a) = (term86 A NIL' CONS' list' a).
Proof. exact (eq_refl (term86 A NIL' CONS' list' a)). Qed.
Lemma lem1070696 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term86 A NIL' CONS' list' a) = (term53 A NIL' a CONS' list').
Proof. exact (eq_refl (term86 A NIL' CONS' list' a)). Qed.
Lemma lem1070697 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term87 A NIL' CONS' list' a) = (term87 A NIL' CONS' list' a).
Proof. exact (eq_refl (term87 A NIL' CONS' list' a)). Qed.
Lemma lem1070698 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : ((term86 A NIL' CONS' list' a) = (term86 A NIL' CONS' list' a)) = ((term86 A NIL' CONS' list' a) = (term53 A NIL' a CONS' list')).
Proof. exact (MK_COMB (@lem1070697 A NIL' CONS' list' a) (@lem1070696 A NIL' a CONS' list')). Qed.
Lemma lem1070699 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term86 A NIL' CONS' list' a) = (term53 A NIL' a CONS' list').
Proof. exact (EQ_MP (@lem1070698 A NIL' a CONS' list') (@lem1070695 A NIL' CONS' list' a)). Qed.
Lemma lem1070700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070701 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term88 A NIL' CONS' list' a) = (term89 A NIL' a CONS' list').
Proof. exact (MK_COMB (@lem1070700) (@lem1070699 A NIL' a CONS' list')). Qed.
Lemma lem1070702 {A : Type'} (list' : type1338 A) (a : recspace A) : (list' a) = (list' a).
Proof. exact (eq_refl (list' a)). Qed.
Lemma lem1070703 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term90 A NIL' CONS' list' a) = (term54 A NIL' CONS' list' a).
Proof. exact (MK_COMB (@lem1070701 A NIL' a CONS' list') (@lem1070702 A list' a)). Qed.
Lemma lem1070704 {A : Type'} (a : recspace A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term91 A a NIL' CONS' list') = (term91 A a NIL' CONS' list').
Proof. exact (eq_refl (term91 A a NIL' CONS' list')). Qed.
Lemma lem1070705 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term92 A NIL' CONS' list' a) = (term93 A NIL' a CONS' list').
Proof. exact (MK_COMB (@lem1070704 A a NIL' CONS' list') (@lem1070699 A NIL' a CONS' list')). Qed.
Lemma lem1070706 {A : Type'} (list' : type1338 A) (a : recspace A) : (term94 A list' a) = (term94 A list' a).
Proof. exact (eq_refl (term94 A list' a)). Qed.
Lemma lem1070707 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term95 A NIL' CONS' list' a) = (term96 A NIL' a CONS' list').
Proof. exact (MK_COMB (@lem1070706 A list' a) (@lem1070699 A NIL' a CONS' list')). Qed.
Lemma lem1070708 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term97 A NIL' CONS' list') = (term98 A NIL' CONS' list').
Proof. exact (fun_ext (fun a : recspace A => @lem1070707 A NIL' a CONS' list')). Qed.
Lemma lem1070709 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1070710 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term99 A NIL' CONS' list') = (term100 A NIL' CONS' list').
Proof. exact (MK_COMB (@lem1070709 A) (@lem1070708 A NIL' CONS' list')). Qed.
Lemma lem1070711 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term101 A NIL' CONS' list') = (term102 A NIL' CONS' list').
Proof. exact (fun_ext (fun a : recspace A => @lem1070705 A NIL' a CONS' list')). Qed.
Lemma lem1070712 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1070713 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term103 A NIL' CONS' list') = (term104 A NIL' CONS' list').
Proof. exact (MK_COMB (@lem1070712 A) (@lem1070711 A NIL' CONS' list')). Qed.
Lemma lem1070714 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term105 A NIL' CONS' list') = (term106 A NIL' CONS' list').
Proof. exact (fun_ext (fun a : recspace A => @lem1070703 A NIL' CONS' list' a)). Qed.
Lemma lem1070715 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1070716 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term107 A NIL' CONS' list') = (term55 A NIL' CONS' list').
Proof. exact (MK_COMB (@lem1070715 A) (@lem1070714 A NIL' CONS' list')). Qed.
Lemma lem1070717 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term55 A NIL' CONS' list') = (term107 A NIL' CONS' list').
Proof. exact (SYM (@lem1070716 A NIL' CONS' list')). Qed.
Lemma lem1070718 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term107 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070717 A NIL' CONS' list') (@lem1070692 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070719 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term108 A NIL' CONS' list'.
Proof. exact (@lem1070660 A NIL' CONS' h1 (term109 A NIL' CONS' list')). Qed.
Lemma lem1070720 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) : (term108 A NIL' CONS' list') = (term110 A list' NIL' CONS').
Proof. exact (eq_refl (term108 A NIL' CONS' list')). Qed.
Lemma lem1070721 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term110 A list' NIL' CONS'.
Proof. exact (EQ_MP (@lem1070720 A list' NIL' CONS') (@lem1070719 A list' NIL' CONS' h1)). Qed.
Lemma lem1070722 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term111 A NIL' CONS' list'.
Proof. exact (@lem1070721 A list' NIL' CONS' h1 list'). Qed.
Lemma lem1070723 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term111 A NIL' CONS' list') = (term112 A NIL' CONS' list').
Proof. exact (eq_refl (term111 A NIL' CONS' list')). Qed.
Lemma lem1070724 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') : term112 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070723 A NIL' CONS' list') (@lem1070722 A list' NIL' CONS' h1)). Qed.
Lemma lem1070725 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term104 A NIL' CONS' list'.
Proof. exact (@lem1070724 A list' NIL' CONS' h1 (@lem1070718 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070726 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term104 A NIL' CONS' list') = (term103 A NIL' CONS' list').
Proof. exact (SYM (@lem1070713 A NIL' CONS' list')). Qed.
Lemma lem1070727 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term103 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070726 A NIL' CONS' list') (@lem1070725 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070728 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term113 A NIL' CONS' list'.
Proof. exact (@lem1070659 A list' NIL' CONS' h1 (term109 A NIL' CONS' list')). Qed.
Lemma lem1070729 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term113 A NIL' CONS' list') = (term114 A NIL' CONS' list').
Proof. exact (eq_refl (term113 A NIL' CONS' list')). Qed.
Lemma lem1070730 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term114 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070729 A NIL' CONS' list') (@lem1070728 A list' NIL' CONS' h1)). Qed.
Lemma lem1070731 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term99 A NIL' CONS' list'.
Proof. exact (@lem1070730 A list' NIL' CONS' h2 (@lem1070727 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070732 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term100 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070710 A NIL' CONS' list') (@lem1070731 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070733 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term56 A NIL' CONS' list' a.
Proof. exact (@lem1070692 A list' NIL' CONS' h1 h2 a). Qed.
Lemma lem1070734 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (a : recspace A) : (term56 A NIL' CONS' list' a) = (term54 A NIL' CONS' list' a).
Proof. exact (eq_refl (term56 A NIL' CONS' list' a)). Qed.
Lemma lem1070735 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term54 A NIL' CONS' list' a.
Proof. exact (EQ_MP (@lem1070734 A NIL' CONS' list' a) (@lem1070733 A a list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070736 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term115 A NIL' CONS' list' a.
Proof. exact (@lem1070732 A list' NIL' CONS' h1 h2 a). Qed.
Lemma lem1070737 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term115 A NIL' CONS' list' a) = (term96 A NIL' a CONS' list').
Proof. exact (eq_refl (term115 A NIL' CONS' list' a)). Qed.
Lemma lem1070738 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term96 A NIL' a CONS' list'.
Proof. exact (EQ_MP (@lem1070737 A NIL' a CONS' list') (@lem1070736 A a list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070739 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term116 A NIL' CONS' list' a.
Proof. exact (conj (@lem1070738 A a list' NIL' CONS' h1 h2) (@lem1070735 A a list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070740 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term116 A NIL' CONS' list' a) = ((list' a) = (term53 A NIL' a CONS' list')).
Proof. exact (@lem32 (list' a) (term53 A NIL' a CONS' list')). Qed.
Lemma lem1070741 {A : Type'} (a : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : (list' a) = (term53 A NIL' a CONS' list').
Proof. exact (EQ_MP (@lem1070740 A NIL' a CONS' list') (@lem1070739 A a list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070746 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term55 A NIL' CONS' list'.
Proof. exact (fun a : recspace A => @lem1070691 A a list' NIL' CONS' h1 h2). Qed.
Lemma lem1070747 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term117 A NIL' CONS' list'.
Proof. exact (fun a : recspace A => @lem1070741 A a list' NIL' CONS' h1 h2). Qed.
Lemma lem1070748 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term73 A NIL' CONS' list'.
Proof. exact (fun list'' : type1338 A => @lem1070658 A list'' list' NIL' CONS' h2). Qed.
Lemma lem1070749 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term49 A NIL' list' CONS'.
Proof. exact (EQ_MP (@lem1070633 A NIL' list' CONS') (@lem1070746 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070763 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (CONS' : type1399 A) : (term55 A NIL' CONS' list') = (term49 A NIL' list' CONS').
Proof. exact (SYM (@lem1070632 A NIL' CONS' list')). Qed.
Lemma lem1070764 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (CONS' : type1399 A) : (term55 A NIL' CONS' list') = (term49 A NIL' list' CONS').
Proof. exact (@lem1070763 A NIL' list' CONS'). Qed.
Lemma lem1070765 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (CONS' : type1399 A) : (term55 A NIL' CONS' list') = (term49 A NIL' list' CONS').
Proof. exact (@lem1070764 A NIL' list' CONS'). Qed.
Lemma lem1070766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070767 {A : Type'} (NIL' : recspace A) (list' : type1338 A) (CONS' : type1399 A) : (term118 A NIL' CONS' list') = (term119 A NIL' list' CONS').
Proof. exact (MK_COMB (@lem1070766) (@lem1070765 A NIL' list' CONS')). Qed.
Lemma lem1070792 {A : Type'} (list' : type1338 A) (list'' : type1338 A) : (term71 A list' list'') = (term71 A list' list'').
Proof. exact (eq_refl (term71 A list' list'')). Qed.
Lemma lem1070793 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) : (term72 A NIL' CONS' list' list'') = (term120 A NIL' CONS' list' list'').
Proof. exact (MK_COMB (@lem1070767 A NIL' list'' CONS') (@lem1070792 A list' list'')). Qed.
Lemma lem1070794 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term121 A NIL' CONS' list') = (term122 A NIL' CONS' list').
Proof. exact (fun_ext (fun list'' : type1338 A => @lem1070793 A NIL' CONS' list' list'')). Qed.
Lemma lem1070795 {A : Type'} : (@all ((recspace A) -> Prop)) = (@all ((recspace A) -> Prop)).
Proof. exact (eq_refl (@all ((recspace A) -> Prop))). Qed.
Lemma lem1070796 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term73 A NIL' CONS' list') = (term123 A NIL' CONS' list').
Proof. exact (MK_COMB (@lem1070795 A) (@lem1070794 A NIL' CONS' list')). Qed.
Lemma lem1070797 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term123 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070796 A NIL' CONS' list') (@lem1070748 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070798 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term124 A NIL' CONS' list'.
Proof. exact (conj (@lem1070797 A list' NIL' CONS' h1 h2) (@lem1070747 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070799 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : term74 A NIL' CONS') (h2 : list' = (term61 A NIL' CONS')) : term125 A NIL' CONS' list'.
Proof. exact (conj (@lem1070749 A list' NIL' CONS' h1 h2) (@lem1070798 A list' NIL' CONS' h1 h2)). Qed.
Lemma lem1070800 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term71 A list' list''.
Proof. exact (h1). Qed.
Lemma lem1070802 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term126 A C B D.
Proof. exact (fun h0 : term127 A B C D => @lem7129 A B C D h0). Qed.
Lemma lem1070804 {A : Type'} (a : recspace A) (NIL' : recspace A) : term128 A a NIL'.
Proof. exact (@lem9120 (a = NIL')). Qed.
Lemma lem1070805 {A : Type'} (a : recspace A) (NIL' : recspace A) : (term128 A a NIL') = (term129 A a NIL').
Proof. exact (eq_refl (term128 A a NIL')). Qed.
Lemma lem1070806 {A : Type'} (a : recspace A) (NIL' : recspace A) : term129 A a NIL'.
Proof. exact (EQ_MP (@lem1070805 A a NIL') (@lem1070804 A a NIL')). Qed.
Lemma lem1070808 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term130 A P Q.
Proof. exact (fun h0 : term131 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1070809 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term130 A P Q.
Proof. exact (@lem1070808 A P Q). Qed.
Lemma lem1070810 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : term132 A list' a CONS' list''.
Proof. exact (@lem1070809 A (term38 A a CONS' list') (term38 A a CONS' list'')). Qed.
Lemma lem1070811 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term133 A a CONS' list' a0) = (term35 A a CONS' a0 list').
Proof. exact (eq_refl (term133 A a CONS' list' a0)). Qed.
Lemma lem1070812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070813 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term134 A a CONS' list' a0) = (term135 A a CONS' a0 list').
Proof. exact (MK_COMB (@lem1070812) (@lem1070811 A a CONS' a0 list')). Qed.
Lemma lem1070814 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term133 A a CONS' list' a0) = (term35 A a CONS' a0 list').
Proof. exact (eq_refl (term133 A a CONS' list' a0)). Qed.
Lemma lem1070815 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : (term136 A list' a CONS' list'' a0) = (term137 A list' a CONS' a0 list'').
Proof. exact (MK_COMB (@lem1070813 A a CONS' a0 list') (@lem1070814 A a CONS' a0 list'')). Qed.
Lemma lem1070816 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term138 A list' a CONS' list'') = (term139 A list' a CONS' list'').
Proof. exact (fun_ext (fun a0 : A => @lem1070815 A list' a CONS' a0 list'')). Qed.
Lemma lem1070817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1070818 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term140 A list' a CONS' list'') = (term141 A list' a CONS' list'').
Proof. exact (MK_COMB (@lem1070817 A) (@lem1070816 A list' a CONS' list'')). Qed.
Lemma lem1070819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070820 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term142 A list' a CONS' list'') = (term143 A list' a CONS' list'').
Proof. exact (MK_COMB (@lem1070819) (@lem1070818 A list' a CONS' list'')). Qed.
Lemma lem1070821 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term133 A a CONS' list' a0) = (term35 A a CONS' a0 list').
Proof. exact (eq_refl (term133 A a CONS' list' a0)). Qed.
Lemma lem1070822 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term144 A a CONS' list') = (term38 A a CONS' list').
Proof. exact (fun_ext (fun a0 : A => @lem1070821 A a CONS' a0 list')). Qed.
Lemma lem1070823 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1070824 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term145 A a CONS' list') = (term37 A a CONS' list').
Proof. exact (MK_COMB (@lem1070823 A) (@lem1070822 A a CONS' list')). Qed.
Lemma lem1070825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070826 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term146 A a CONS' list') = (term147 A a CONS' list').
Proof. exact (MK_COMB (@lem1070825) (@lem1070824 A a CONS' list')). Qed.
Lemma lem1070827 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term133 A a CONS' list' a0) = (term35 A a CONS' a0 list').
Proof. exact (eq_refl (term133 A a CONS' list' a0)). Qed.
Lemma lem1070828 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term144 A a CONS' list') = (term38 A a CONS' list').
Proof. exact (fun_ext (fun a0 : A => @lem1070827 A a CONS' a0 list')). Qed.
Lemma lem1070829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1070830 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) : (term145 A a CONS' list') = (term37 A a CONS' list').
Proof. exact (MK_COMB (@lem1070829 A) (@lem1070828 A a CONS' list')). Qed.
Lemma lem1070831 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term148 A list' a CONS' list'') = (term149 A list' a CONS' list'').
Proof. exact (MK_COMB (@lem1070826 A a CONS' list') (@lem1070830 A a CONS' list'')). Qed.
Lemma lem1070832 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : (term132 A list' a CONS' list'') = (term150 A list' a CONS' list'').
Proof. exact (MK_COMB (@lem1070820 A list' a CONS' list'') (@lem1070831 A list' a CONS' list'')). Qed.
Lemma lem1070835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term130 A P Q.
Proof. exact (fun h0 : term131 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1070836 {A : Type'} (P : type1338 A) (Q : type1338 A) : term151 A P Q.
Proof. exact (@lem1070835 (recspace A) P Q). Qed.
Lemma lem1070837 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : term152 A list' a CONS' a0 list''.
Proof. exact (@lem1070836 A (term36 A a CONS' a0 list') (term36 A a CONS' a0 list'')). Qed.
Lemma lem1070838 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) : (term153 A a CONS' a0 list' a1) = (term11 A a CONS' a0 list' a1).
Proof. exact (eq_refl (term153 A a CONS' a0 list' a1)). Qed.
Lemma lem1070839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070840 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) : (term154 A a CONS' a0 list' a1) = (term155 A a CONS' a0 list' a1).
Proof. exact (MK_COMB (@lem1070839) (@lem1070838 A a CONS' a0 list' a1)). Qed.
Lemma lem1070841 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) : (term153 A a CONS' a0 list' a1) = (term11 A a CONS' a0 list' a1).
Proof. exact (eq_refl (term153 A a CONS' a0 list' a1)). Qed.
Lemma lem1070842 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) (a1 : recspace A) : (term156 A list' a CONS' a0 list'' a1) = (term157 A list' a CONS' a0 list'' a1).
Proof. exact (MK_COMB (@lem1070840 A a CONS' a0 list' a1) (@lem1070841 A a CONS' a0 list'' a1)). Qed.
Lemma lem1070843 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : (term158 A list' a CONS' a0 list'') = (term159 A list' a CONS' a0 list'').
Proof. exact (fun_ext (fun a1 : recspace A => @lem1070842 A list' a CONS' a0 list'' a1)). Qed.
Lemma lem1070844 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1070845 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : (term160 A list' a CONS' a0 list'') = (term161 A list' a CONS' a0 list'').
Proof. exact (MK_COMB (@lem1070844 A) (@lem1070843 A list' a CONS' a0 list'')). Qed.
Lemma lem1070846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070847 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : (term162 A list' a CONS' a0 list'') = (term163 A list' a CONS' a0 list'').
Proof. exact (MK_COMB (@lem1070846) (@lem1070845 A list' a CONS' a0 list'')). Qed.
Lemma lem1070848 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) : (term153 A a CONS' a0 list' a1) = (term11 A a CONS' a0 list' a1).
Proof. exact (eq_refl (term153 A a CONS' a0 list' a1)). Qed.
Lemma lem1070849 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term164 A a CONS' a0 list') = (term36 A a CONS' a0 list').
Proof. exact (fun_ext (fun a1 : recspace A => @lem1070848 A a CONS' a0 list' a1)). Qed.
Lemma lem1070850 {A : Type'} : (@ex (recspace A)) = (@ex (recspace A)).
Proof. exact (eq_refl (@ex (recspace A))). Qed.
Lemma lem1070851 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term165 A a CONS' a0 list') = (term35 A a CONS' a0 list').
Proof. exact (MK_COMB (@lem1070850 A) (@lem1070849 A a CONS' a0 list')). Qed.
Lemma lem1070852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070853 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term166 A a CONS' a0 list') = (term135 A a CONS' a0 list').
Proof. exact (MK_COMB (@lem1070852) (@lem1070851 A a CONS' a0 list')). Qed.
Lemma lem1070854 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (a1 : recspace A) : (term153 A a CONS' a0 list' a1) = (term11 A a CONS' a0 list' a1).
Proof. exact (eq_refl (term153 A a CONS' a0 list' a1)). Qed.
Lemma lem1070855 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term164 A a CONS' a0 list') = (term36 A a CONS' a0 list').
Proof. exact (fun_ext (fun a1 : recspace A => @lem1070854 A a CONS' a0 list' a1)). Qed.
Lemma lem1070856 {A : Type'} : (@ex (recspace A)) = (@ex (recspace A)).
Proof. exact (eq_refl (@ex (recspace A))). Qed.
Lemma lem1070857 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) : (term165 A a CONS' a0 list') = (term35 A a CONS' a0 list').
Proof. exact (MK_COMB (@lem1070856 A) (@lem1070855 A a CONS' a0 list')). Qed.
Lemma lem1070858 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : (term167 A list' a CONS' a0 list'') = (term137 A list' a CONS' a0 list'').
Proof. exact (MK_COMB (@lem1070853 A a CONS' a0 list') (@lem1070857 A a CONS' a0 list'')). Qed.
Lemma lem1070859 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : (term152 A list' a CONS' a0 list'') = (term168 A list' a CONS' a0 list'').
Proof. exact (MK_COMB (@lem1070847 A list' a CONS' a0 list'') (@lem1070858 A list' a CONS' a0 list'')). Qed.
Lemma lem1070862 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term169 A C B D.
Proof. exact (fun h0 : term127 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem1070864 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : term170 A a CONS' a0 a1.
Proof. exact (@lem9120 (a = (CONS' a0 a1))). Qed.
Lemma lem1070865 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term170 A a CONS' a0 a1) = (term171 A a CONS' a0 a1).
Proof. exact (eq_refl (term170 A a CONS' a0 a1)). Qed.
Lemma lem1070866 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : term171 A a CONS' a0 a1.
Proof. exact (EQ_MP (@lem1070865 A a CONS' a0 a1) (@lem1070864 A a CONS' a0 a1)). Qed.
Lemma lem1070867 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term172 A list' list'' a.
Proof. exact (@lem1070800 A list' list'' h1 a). Qed.
Lemma lem1070868 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (a : recspace A) : (term172 A list' list'' a) = (term70 A list' list'' a).
Proof. exact (eq_refl (term172 A list' list'' a)). Qed.
Lemma lem1070869 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term70 A list' list'' a.
Proof. exact (EQ_MP (@lem1070868 A list' list'' a) (@lem1070867 A a list' list'' h1)). Qed.
Lemma lem1070870 {A : Type'} (list' : type1338 A) (list'' : type1338 A) (a : recspace A) : (term70 A list' list'' a) = ((term70 A list' list'' a) = True).
Proof. exact (@lem7 (term70 A list' list'' a)). Qed.
Lemma lem1070873 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : (term70 A list' list'' a) = True.
Proof. exact (EQ_MP (@lem1070870 A list' list'' a) (@lem1070869 A a list' list'' h1)). Qed.
Lemma lem1070874 {A : Type'} (a : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : (term70 A list' list'' a) = True.
Proof. exact (@lem1070873 A a list' list'' h1). Qed.
Lemma lem1070875 {A : Type'} (a1 : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : (term70 A list' list'' a1) = True.
Proof. exact (@lem1070874 A a1 list' list'' h1). Qed.
Lemma lem1070876 {A : Type'} (a1 : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : True = (term70 A list' list'' a1).
Proof. exact (SYM (@lem1070875 A a1 list' list'' h1)). Qed.
Lemma lem1070877 {A : Type'} (a1 : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term70 A list' list'' a1.
Proof. exact (EQ_MP (@lem1070876 A a1 list' list'' h1) (@lem0)). Qed.
Lemma lem1070878 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term173 A a CONS' a0 list' list'' a1.
Proof. exact (conj (@lem1070866 A a CONS' a0 a1) (@lem1070877 A a1 list' list'' h1)). Qed.
Lemma lem1070880 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) (a1 : recspace A) : term174 A list' a CONS' a0 list'' a1.
Proof. exact (@lem1070862 (a = (CONS' a0 a1)) (list' a1) (a = (CONS' a0 a1)) (list'' a1)). Qed.
Lemma lem1070881 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) (a1 : recspace A) : term174 A list' a CONS' a0 list'' a1.
Proof. exact (@lem1070880 A list' a CONS' a0 list'' a1). Qed.
Lemma lem1070882 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term157 A list' a CONS' a0 list'' a1.
Proof. exact (@lem1070881 A list' a CONS' a0 list'' a1 (@lem1070878 A a CONS' a0 a1 list' list'' h1)). Qed.
Lemma lem1070887 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term161 A list' a CONS' a0 list''.
Proof. exact (fun a1 : recspace A => @lem1070882 A a CONS' a0 a1 list' list'' h1). Qed.
Lemma lem1070889 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : term168 A list' a CONS' a0 list''.
Proof. exact (EQ_MP (@lem1070859 A list' a CONS' a0 list'') (@lem1070837 A list' a CONS' a0 list'')). Qed.
Lemma lem1070890 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (a0 : A) (list'' : type1338 A) : term168 A list' a CONS' a0 list''.
Proof. exact (@lem1070889 A list' a CONS' a0 list''). Qed.
Lemma lem1070891 {A : Type'} (a : recspace A) (CONS' : type1399 A) (a0 : A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term137 A list' a CONS' a0 list''.
Proof. exact (@lem1070890 A list' a CONS' a0 list'' (@lem1070887 A a CONS' a0 list' list'' h1)). Qed.
Lemma lem1070896 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term141 A list' a CONS' list''.
Proof. exact (fun a0 : A => @lem1070891 A a CONS' a0 list' list'' h1). Qed.
Lemma lem1070898 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : term150 A list' a CONS' list''.
Proof. exact (EQ_MP (@lem1070832 A list' a CONS' list'') (@lem1070810 A list' a CONS' list'')). Qed.
Lemma lem1070899 {A : Type'} (list' : type1338 A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : term150 A list' a CONS' list''.
Proof. exact (@lem1070898 A list' a CONS' list''). Qed.
Lemma lem1070900 {A : Type'} (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term149 A list' a CONS' list''.
Proof. exact (@lem1070899 A list' a CONS' list'' (@lem1070896 A a CONS' list' list'' h1)). Qed.
Lemma lem1070901 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term175 A NIL' list' a CONS' list''.
Proof. exact (conj (@lem1070806 A a NIL') (@lem1070900 A a CONS' list' list'' h1)). Qed.
Lemma lem1070903 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : term176 A list' NIL' a CONS' list''.
Proof. exact (@lem1070802 (a = NIL') (term37 A a CONS' list') (a = NIL') (term37 A a CONS' list'')). Qed.
Lemma lem1070904 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : term176 A list' NIL' a CONS' list''.
Proof. exact (@lem1070903 A list' NIL' a CONS' list''). Qed.
Lemma lem1070905 {A : Type'} (NIL' : recspace A) (a : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term82 A list' NIL' a CONS' list''.
Proof. exact (@lem1070904 A list' NIL' a CONS' list'' (@lem1070901 A NIL' a CONS' list' list'' h1)). Qed.
Lemma lem1070910 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term80 A list' NIL' CONS' list''.
Proof. exact (fun a : recspace A => @lem1070905 A NIL' a CONS' list' list'' h1). Qed.
Lemma lem1070911 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : (term71 A list' list'') = (term80 A list' NIL' CONS' list'').
Proof. exact (prop_ext (fun h2 : term71 A list' list'' => @lem1070910 A NIL' CONS' list' list'' h1) (fun h2 : term80 A list' NIL' CONS' list'' => @lem1070800 A list' list'' h1)). Qed.
Lemma lem1070912 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (list'' : type1338 A) (h1 : term71 A list' list'') : term80 A list' NIL' CONS' list''.
Proof. exact (EQ_MP (@lem1070911 A NIL' CONS' list' list'' h1) (@lem1070800 A list' list'' h1)). Qed.
Lemma lem1070913 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (list'' : type1338 A) : term79 A list' NIL' CONS' list''.
Proof. exact (fun h0 : term71 A list' list'' => @lem1070912 A NIL' CONS' list' list'' h0). Qed.
Lemma lem1070918 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) : term77 A list' NIL' CONS'.
Proof. exact (fun list'' : type1338 A => @lem1070913 A list' NIL' CONS' list''). Qed.
Lemma lem1070923 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : term74 A NIL' CONS'.
Proof. exact (fun list' : type1338 A => @lem1070918 A list' NIL' CONS'). Qed.
Lemma lem1070924 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : (term74 A NIL' CONS') = (term125 A NIL' CONS' list').
Proof. exact (prop_ext (fun h2 : term74 A NIL' CONS' => @lem1070799 A list' NIL' CONS' h2 h1) (fun h2 : term125 A NIL' CONS' list' => @lem1070923 A NIL' CONS')). Qed.
Lemma lem1070925 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term61 A NIL' CONS')) : term125 A NIL' CONS' list'.
Proof. exact (EQ_MP (@lem1070924 A list' NIL' CONS' h1) (@lem1070923 A NIL' CONS')). Qed.
