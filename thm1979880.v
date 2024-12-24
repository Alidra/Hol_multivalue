Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1979880_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RAT_LEMMA4_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm7_spec.
Lemma lem1979408 (x1 : real) (y2 : real) (x2 : real) (y1 : real) (h1 : term0 x1 y2 x2 y1) : term0 x1 y2 x2 y1.
Proof. exact (h1). Qed.
Lemma lem1979409 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term1 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1979410 (x1 : real) (y2 : real) (x2 : real) (y1 : real) (h1 : term1 y1 y2) (h2 : term0 x1 y2 x2 y1) : (term2 x1 y1 x2 y2) = (term3 x1 y2 x2 y1).
Proof. exact (@lem1979408 x1 y2 x2 y1 h2 (@lem1979409 y1 y2 h1)). Qed.
Lemma lem1979411 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term4 x1 y2 x2 y1.
Proof. exact (fun h0 : term0 x1 y2 x2 y1 => @lem1979410 x1 y2 x2 y1 h1 h0). Qed.
Lemma lem1979412 (x1 : real) (y2 : real) (x2 : real) (y1 : real) (h1 : term0 x1 y2 x2 y1) : term0 x1 y2 x2 y1.
Proof. exact (h1). Qed.
Lemma lem1979413 (x1 : real) (y2 : real) (x2 : real) (y1 : real) (h1 : term1 y1 y2) (h2 : term0 x1 y2 x2 y1) : (term2 x1 y1 x2 y2) = (term3 x1 y2 x2 y1).
Proof. exact (@lem1979411 x1 x2 y1 y2 h1 (@lem1979412 x1 y2 x2 y1 h2)). Qed.
Lemma lem1979414 (x1 : real) (y2 : real) (x2 : real) (y1 : real) (h1 : term0 x1 y2 x2 y1) : term0 x1 y2 x2 y1.
Proof. exact (fun h0 : term1 y1 y2 => @lem1979413 x1 y2 x2 y1 h0 h1). Qed.
Lemma lem1979415 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term5 x1 y2 x2 y1.
Proof. exact (fun h0 : term0 x1 y2 x2 y1 => @lem1979414 x1 y2 x2 y1 h0). Qed.
Lemma lem1979433 (a : Prop) : term6 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem1979434 (a : Prop) : (term6 a) = (term7 a).
Proof. exact (eq_refl (term6 a)). Qed.
Lemma lem1979435 (a : Prop) : term7 a.
Proof. exact (EQ_MP (@lem1979434 a) (@lem1979433 a)). Qed.
Lemma lem1979436 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem1979437 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem1979454 (b : Prop) (a' : Prop) (b' : Prop) : (term8 b a' b') = (term8 b a' b').
Proof. exact (eq_refl (term8 b a' b')). Qed.
Lemma lem1979455 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = True) : (term9 b a' b' a) = (term10 b a' b').
Proof. exact (MK_COMB (@lem1979454 b a' b') (@lem1979436 a h1)). Qed.
Lemma lem1979456 (b : Prop) (a' : Prop) (b' : Prop) : (term10 b a' b') = (term11 b a' b').
Proof. exact (eq_refl (term10 b a' b')). Qed.
Lemma lem1979457 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) : (term12 b a' b' a) = (term12 b a' b' a).
Proof. exact (eq_refl (term12 b a' b' a)). Qed.
Lemma lem1979458 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : ((term9 b a' b' a) = (term10 b a' b')) = ((term9 b a' b' a) = (term11 b a' b')).
Proof. exact (MK_COMB (@lem1979457 b a' b' a) (@lem1979456 b a' b')). Qed.
Lemma lem1979459 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : (term9 b a' b' a) = (term13 a b a' b').
Proof. exact (eq_refl (term9 b a' b' a)). Qed.
Lemma lem1979460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979461 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : (term12 b a' b' a) = (term14 a b a' b').
Proof. exact (MK_COMB (@lem1979460) (@lem1979459 a b a' b')). Qed.
Lemma lem1979462 (b : Prop) (a' : Prop) (b' : Prop) : (term11 b a' b') = (term11 b a' b').
Proof. exact (eq_refl (term11 b a' b')). Qed.
Lemma lem1979463 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : ((term9 b a' b' a) = (term11 b a' b')) = ((term13 a b a' b') = (term11 b a' b')).
Proof. exact (MK_COMB (@lem1979461 a b a' b') (@lem1979462 b a' b')). Qed.
Lemma lem1979464 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : ((term9 b a' b' a) = (term10 b a' b')) = ((term13 a b a' b') = (term11 b a' b')).
Proof. exact (TRANS (@lem1979458 a b a' b') (@lem1979463 a b a' b')). Qed.
Lemma lem1979465 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = True) : (term13 a b a' b') = (term11 b a' b').
Proof. exact (EQ_MP (@lem1979464 a b a' b') (@lem1979455 b a' b' a h1)). Qed.
Lemma lem1979466 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = True) : (term11 b a' b') = (term13 a b a' b').
Proof. exact (SYM (@lem1979465 b a' b' a h1)). Qed.
Lemma lem1979467 (b : Prop) (a' : Prop) (b' : Prop) : (term8 b a' b') = (term8 b a' b').
Proof. exact (eq_refl (term8 b a' b')). Qed.
Lemma lem1979468 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = False) : (term9 b a' b' a) = (term15 b a' b').
Proof. exact (MK_COMB (@lem1979467 b a' b') (@lem1979437 a h1)). Qed.
Lemma lem1979469 (b : Prop) (a' : Prop) (b' : Prop) : (term15 b a' b') = (term16 b a' b').
Proof. exact (eq_refl (term15 b a' b')). Qed.
Lemma lem1979470 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) : (term12 b a' b' a) = (term12 b a' b' a).
Proof. exact (eq_refl (term12 b a' b' a)). Qed.
Lemma lem1979471 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : ((term9 b a' b' a) = (term15 b a' b')) = ((term9 b a' b' a) = (term16 b a' b')).
Proof. exact (MK_COMB (@lem1979470 b a' b' a) (@lem1979469 b a' b')). Qed.
Lemma lem1979472 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : (term9 b a' b' a) = (term13 a b a' b').
Proof. exact (eq_refl (term9 b a' b' a)). Qed.
Lemma lem1979473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979474 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : (term12 b a' b' a) = (term14 a b a' b').
Proof. exact (MK_COMB (@lem1979473) (@lem1979472 a b a' b')). Qed.
Lemma lem1979475 (b : Prop) (a' : Prop) (b' : Prop) : (term16 b a' b') = (term16 b a' b').
Proof. exact (eq_refl (term16 b a' b')). Qed.
Lemma lem1979476 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : ((term9 b a' b' a) = (term16 b a' b')) = ((term13 a b a' b') = (term16 b a' b')).
Proof. exact (MK_COMB (@lem1979474 a b a' b') (@lem1979475 b a' b')). Qed.
Lemma lem1979477 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : ((term9 b a' b' a) = (term15 b a' b')) = ((term13 a b a' b') = (term16 b a' b')).
Proof. exact (TRANS (@lem1979471 a b a' b') (@lem1979476 a b a' b')). Qed.
Lemma lem1979478 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = False) : (term13 a b a' b') = (term16 b a' b').
Proof. exact (EQ_MP (@lem1979477 a b a' b') (@lem1979468 b a' b' a h1)). Qed.
Lemma lem1979479 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = False) : (term16 b a' b') = (term13 a b a' b').
Proof. exact (SYM (@lem1979478 b a' b' a h1)). Qed.
Lemma lem1979485 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1979486 (a' : Prop) : (True = a') = a'.
Proof. exact (@lem1979485 a'). Qed.
Lemma lem1979487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979488 (a' : Prop) : (term17 a') = (and a').
Proof. exact (MK_COMB (@lem1979487) (@lem1979486 a')). Qed.
Lemma lem1979491 (b : Prop) (b' : Prop) : (b = b') = (b = b').
Proof. exact (eq_refl (b = b')). Qed.
Lemma lem1979492 (a' : Prop) (b : Prop) (b' : Prop) : (term18 a' b b') = (term19 a' b b').
Proof. exact (MK_COMB (@lem1979488 a') (@lem1979491 b b')). Qed.
Lemma lem1979495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979496 (a' : Prop) (b : Prop) (b' : Prop) : (term20 a' b b') = (term21 a' b b').
Proof. exact (MK_COMB (@lem1979495) (@lem1979492 a' b b')). Qed.
Lemma lem1979500 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979501 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem1979500 b). Qed.
Lemma lem1979502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979503 (b : Prop) : (term22 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem1979502) (@lem1979501 b)). Qed.
Lemma lem1979506 (a' : Prop) (b' : Prop) : (a' /\ b') = (a' /\ b').
Proof. exact (eq_refl (a' /\ b')). Qed.
Lemma lem1979507 (b : Prop) (a' : Prop) (b' : Prop) : ((True /\ b) = (a' /\ b')) = (b = (a' /\ b')).
Proof. exact (MK_COMB (@lem1979503 b) (@lem1979506 a' b')). Qed.
Lemma lem1979510 (b : Prop) (a' : Prop) (b' : Prop) : (term11 b a' b') = (term23 b a' b').
Proof. exact (MK_COMB (@lem1979496 a' b b') (@lem1979507 b a' b')). Qed.
Lemma lem1979513 (b : Prop) (a' : Prop) (b' : Prop) : (term23 b a' b') = (term11 b a' b').
Proof. exact (SYM (@lem1979510 b a' b')). Qed.
Lemma lem1979514 (a' : Prop) : term6 a'.
Proof. exact (@lem9851 a'). Qed.
Lemma lem1979515 (a' : Prop) : (term6 a') = (term7 a').
Proof. exact (eq_refl (term6 a')). Qed.
Lemma lem1979516 (a' : Prop) : term7 a'.
Proof. exact (EQ_MP (@lem1979515 a') (@lem1979514 a')). Qed.
Lemma lem1979517 (a' : Prop) (h1 : a' = True) : a' = True.
Proof. exact (h1). Qed.
Lemma lem1979518 (a' : Prop) (h1 : a' = False) : a' = False.
Proof. exact (h1). Qed.
Lemma lem1979531 (b : Prop) (b' : Prop) : (term24 b b') = (term24 b b').
Proof. exact (eq_refl (term24 b b')). Qed.
Lemma lem1979532 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : (term25 b b' a') = (term26 b b').
Proof. exact (MK_COMB (@lem1979531 b b') (@lem1979517 a' h1)). Qed.
Lemma lem1979533 (b : Prop) (b' : Prop) : (term26 b b') = (term27 b b').
Proof. exact (eq_refl (term26 b b')). Qed.
Lemma lem1979534 (b : Prop) (b' : Prop) (a' : Prop) : (term28 b b' a') = (term28 b b' a').
Proof. exact (eq_refl (term28 b b' a')). Qed.
Lemma lem1979535 (a' : Prop) (b : Prop) (b' : Prop) : ((term25 b b' a') = (term26 b b')) = ((term25 b b' a') = (term27 b b')).
Proof. exact (MK_COMB (@lem1979534 b b' a') (@lem1979533 b b')). Qed.
Lemma lem1979536 (b : Prop) (a' : Prop) (b' : Prop) : (term25 b b' a') = (term23 b a' b').
Proof. exact (eq_refl (term25 b b' a')). Qed.
Lemma lem1979537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979538 (b : Prop) (a' : Prop) (b' : Prop) : (term28 b b' a') = (term29 b a' b').
Proof. exact (MK_COMB (@lem1979537) (@lem1979536 b a' b')). Qed.
Lemma lem1979539 (b : Prop) (b' : Prop) : (term27 b b') = (term27 b b').
Proof. exact (eq_refl (term27 b b')). Qed.
Lemma lem1979540 (a' : Prop) (b : Prop) (b' : Prop) : ((term25 b b' a') = (term27 b b')) = ((term23 b a' b') = (term27 b b')).
Proof. exact (MK_COMB (@lem1979538 b a' b') (@lem1979539 b b')). Qed.
Lemma lem1979541 (a' : Prop) (b : Prop) (b' : Prop) : ((term25 b b' a') = (term26 b b')) = ((term23 b a' b') = (term27 b b')).
Proof. exact (TRANS (@lem1979535 a' b b') (@lem1979540 a' b b')). Qed.
Lemma lem1979542 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : (term23 b a' b') = (term27 b b').
Proof. exact (EQ_MP (@lem1979541 a' b b') (@lem1979532 b b' a' h1)). Qed.
Lemma lem1979543 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : (term27 b b') = (term23 b a' b').
Proof. exact (SYM (@lem1979542 b b' a' h1)). Qed.
Lemma lem1979544 (b : Prop) (b' : Prop) : (term24 b b') = (term24 b b').
Proof. exact (eq_refl (term24 b b')). Qed.
Lemma lem1979545 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : (term25 b b' a') = (term30 b b').
Proof. exact (MK_COMB (@lem1979544 b b') (@lem1979518 a' h1)). Qed.
Lemma lem1979546 (b : Prop) (b' : Prop) : (term30 b b') = (term31 b b').
Proof. exact (eq_refl (term30 b b')). Qed.
Lemma lem1979547 (b : Prop) (b' : Prop) (a' : Prop) : (term28 b b' a') = (term28 b b' a').
Proof. exact (eq_refl (term28 b b' a')). Qed.
Lemma lem1979548 (a' : Prop) (b : Prop) (b' : Prop) : ((term25 b b' a') = (term30 b b')) = ((term25 b b' a') = (term31 b b')).
Proof. exact (MK_COMB (@lem1979547 b b' a') (@lem1979546 b b')). Qed.
Lemma lem1979549 (b : Prop) (a' : Prop) (b' : Prop) : (term25 b b' a') = (term23 b a' b').
Proof. exact (eq_refl (term25 b b' a')). Qed.
Lemma lem1979550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979551 (b : Prop) (a' : Prop) (b' : Prop) : (term28 b b' a') = (term29 b a' b').
Proof. exact (MK_COMB (@lem1979550) (@lem1979549 b a' b')). Qed.
Lemma lem1979552 (b : Prop) (b' : Prop) : (term31 b b') = (term31 b b').
Proof. exact (eq_refl (term31 b b')). Qed.
Lemma lem1979553 (a' : Prop) (b : Prop) (b' : Prop) : ((term25 b b' a') = (term31 b b')) = ((term23 b a' b') = (term31 b b')).
Proof. exact (MK_COMB (@lem1979551 b a' b') (@lem1979552 b b')). Qed.
Lemma lem1979554 (a' : Prop) (b : Prop) (b' : Prop) : ((term25 b b' a') = (term30 b b')) = ((term23 b a' b') = (term31 b b')).
Proof. exact (TRANS (@lem1979548 a' b b') (@lem1979553 a' b b')). Qed.
Lemma lem1979555 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : (term23 b a' b') = (term31 b b').
Proof. exact (EQ_MP (@lem1979554 a' b b') (@lem1979545 b b' a' h1)). Qed.
Lemma lem1979556 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : (term31 b b') = (term23 b a' b').
Proof. exact (SYM (@lem1979555 b b' a' h1)). Qed.
Lemma lem1979560 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979561 (b : Prop) (b' : Prop) : (term32 b b') = (b = b').
Proof. exact (@lem1979560 (b = b')). Qed.
Lemma lem1979564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979565 (b : Prop) (b' : Prop) : (term33 b b') = (term34 b b').
Proof. exact (MK_COMB (@lem1979564) (@lem1979561 b b')). Qed.
Lemma lem1979569 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979570 (b' : Prop) : (True /\ b') = b'.
Proof. exact (@lem1979569 b'). Qed.
Lemma lem1979571 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem1979572 (b : Prop) (b' : Prop) : (b = (True /\ b')) = (b = b').
Proof. exact (MK_COMB (@lem1979571 b) (@lem1979570 b')). Qed.
Lemma lem1979575 (b : Prop) (b' : Prop) : (term27 b b') = (term35 b b').
Proof. exact (MK_COMB (@lem1979565 b b') (@lem1979572 b b')). Qed.
Lemma lem1979579 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1979580 (b : Prop) (b' : Prop) : (term35 b b') = True.
Proof. exact (@lem1979579 (b = b')). Qed.
Lemma lem1979581 (b : Prop) (b' : Prop) : (term27 b b') = True.
Proof. exact (TRANS (@lem1979575 b b') (@lem1979580 b b')). Qed.
Lemma lem1979582 (b : Prop) (b' : Prop) : True = (term27 b b').
Proof. exact (SYM (@lem1979581 b b')). Qed.
Lemma lem1979583 (b : Prop) (b' : Prop) : term27 b b'.
Proof. exact (EQ_MP (@lem1979582 b b') (@lem0)). Qed.
Lemma lem1979587 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1979588 (b : Prop) (b' : Prop) : (term36 b b') = False.
Proof. exact (@lem1979587 (b = b')). Qed.
Lemma lem1979589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979590 (b : Prop) (b' : Prop) : (term37 b b') = (imp False).
Proof. exact (MK_COMB (@lem1979589) (@lem1979588 b b')). Qed.
Lemma lem1979594 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1979595 (b' : Prop) : (False /\ b') = False.
Proof. exact (@lem1979594 b'). Qed.
Lemma lem1979596 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem1979597 (b' : Prop) (b : Prop) : (b = (False /\ b')) = (b = False).
Proof. exact (MK_COMB (@lem1979596 b) (@lem1979595 b')). Qed.
Lemma lem1979599 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1979600 (b : Prop) : (b = False) = (~ b).
Proof. exact (@lem1979599 b). Qed.
Lemma lem1979601 (b' : Prop) (b : Prop) : (b = (False /\ b')) = (~ b).
Proof. exact (TRANS (@lem1979597 b' b) (@lem1979600 b)). Qed.
Lemma lem1979602 (b' : Prop) (b : Prop) : (term31 b b') = (term38 b).
Proof. exact (MK_COMB (@lem1979590 b b') (@lem1979601 b' b)). Qed.
Lemma lem1979604 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1979605 (b : Prop) : (term38 b) = True.
Proof. exact (@lem1979604 (~ b)). Qed.
Lemma lem1979606 (b : Prop) (b' : Prop) : (term31 b b') = True.
Proof. exact (TRANS (@lem1979602 b' b) (@lem1979605 b)). Qed.
Lemma lem1979607 (b : Prop) (b' : Prop) : True = (term31 b b').
Proof. exact (SYM (@lem1979606 b b')). Qed.
Lemma lem1979608 (b : Prop) (b' : Prop) : term31 b b'.
Proof. exact (EQ_MP (@lem1979607 b b') (@lem0)). Qed.
Lemma lem1979609 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : term23 b a' b'.
Proof. exact (EQ_MP (@lem1979556 b b' a' h1) (@lem1979608 b b')). Qed.
Lemma lem1979610 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : term23 b a' b'.
Proof. exact (EQ_MP (@lem1979543 b b' a' h1) (@lem1979583 b b')). Qed.
Lemma lem1979612 (b : Prop) (a' : Prop) (b' : Prop) : term23 b a' b'.
Proof. exact (or_elim (@lem1979516 a') (fun h0 : a' = True => @lem1979610 b b' a' h0) (fun h0 : a' = False => @lem1979609 b b' a' h0)). Qed.
Lemma lem1979613 (b : Prop) (a' : Prop) (b' : Prop) : term11 b a' b'.
Proof. exact (EQ_MP (@lem1979513 b a' b') (@lem1979612 b a' b')). Qed.
Lemma lem1979619 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1979620 (a' : Prop) : (False = a') = (~ a').
Proof. exact (@lem1979619 a'). Qed.
Lemma lem1979621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979622 (a' : Prop) : (term39 a') = (term40 a').
Proof. exact (MK_COMB (@lem1979621) (@lem1979620 a')). Qed.
Lemma lem1979625 (b : Prop) (b' : Prop) : (b = b') = (b = b').
Proof. exact (eq_refl (b = b')). Qed.
Lemma lem1979626 (a' : Prop) (b : Prop) (b' : Prop) : (term41 a' b b') = (term42 a' b b').
Proof. exact (MK_COMB (@lem1979622 a') (@lem1979625 b b')). Qed.
Lemma lem1979629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979630 (a' : Prop) (b : Prop) (b' : Prop) : (term43 a' b b') = (term44 a' b b').
Proof. exact (MK_COMB (@lem1979629) (@lem1979626 a' b b')). Qed.
Lemma lem1979634 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1979635 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem1979634 b). Qed.
Lemma lem1979636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979637 (b : Prop) : (term45 b) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1979636) (@lem1979635 b)). Qed.
Lemma lem1979640 (a' : Prop) (b' : Prop) : (a' /\ b') = (a' /\ b').
Proof. exact (eq_refl (a' /\ b')). Qed.
Lemma lem1979641 (b : Prop) (a' : Prop) (b' : Prop) : ((False /\ b) = (a' /\ b')) = (False = (a' /\ b')).
Proof. exact (MK_COMB (@lem1979637 b) (@lem1979640 a' b')). Qed.
Lemma lem1979643 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1979644 (a' : Prop) (b' : Prop) : (False = (a' /\ b')) = (term46 a' b').
Proof. exact (@lem1979643 (a' /\ b')). Qed.
Lemma lem1979647 (b : Prop) (a' : Prop) (b' : Prop) : ((False /\ b) = (a' /\ b')) = (term46 a' b').
Proof. exact (TRANS (@lem1979641 b a' b') (@lem1979644 a' b')). Qed.
Lemma lem1979648 (b : Prop) (a' : Prop) (b' : Prop) : (term16 b a' b') = (term47 b a' b').
Proof. exact (MK_COMB (@lem1979630 a' b b') (@lem1979647 b a' b')). Qed.
Lemma lem1979651 (b : Prop) (a' : Prop) (b' : Prop) : (term47 b a' b') = (term16 b a' b').
Proof. exact (SYM (@lem1979648 b a' b')). Qed.
Lemma lem1979652 (a' : Prop) : term6 a'.
Proof. exact (@lem9851 a'). Qed.
Lemma lem1979653 (a' : Prop) : (term6 a') = (term7 a').
Proof. exact (eq_refl (term6 a')). Qed.
Lemma lem1979654 (a' : Prop) : term7 a'.
Proof. exact (EQ_MP (@lem1979653 a') (@lem1979652 a')). Qed.
Lemma lem1979655 (a' : Prop) (h1 : a' = True) : a' = True.
Proof. exact (h1). Qed.
Lemma lem1979656 (a' : Prop) (h1 : a' = False) : a' = False.
Proof. exact (h1). Qed.
Lemma lem1979667 (b : Prop) (b' : Prop) : (term48 b b') = (term48 b b').
Proof. exact (eq_refl (term48 b b')). Qed.
Lemma lem1979668 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : (term49 b b' a') = (term50 b b').
Proof. exact (MK_COMB (@lem1979667 b b') (@lem1979655 a' h1)). Qed.
Lemma lem1979669 (b : Prop) (b' : Prop) : (term50 b b') = (term51 b b').
Proof. exact (eq_refl (term50 b b')). Qed.
Lemma lem1979670 (b : Prop) (b' : Prop) (a' : Prop) : (term52 b b' a') = (term52 b b' a').
Proof. exact (eq_refl (term52 b b' a')). Qed.
Lemma lem1979671 (a' : Prop) (b : Prop) (b' : Prop) : ((term49 b b' a') = (term50 b b')) = ((term49 b b' a') = (term51 b b')).
Proof. exact (MK_COMB (@lem1979670 b b' a') (@lem1979669 b b')). Qed.
Lemma lem1979672 (b : Prop) (a' : Prop) (b' : Prop) : (term49 b b' a') = (term47 b a' b').
Proof. exact (eq_refl (term49 b b' a')). Qed.
Lemma lem1979673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979674 (b : Prop) (a' : Prop) (b' : Prop) : (term52 b b' a') = (term53 b a' b').
Proof. exact (MK_COMB (@lem1979673) (@lem1979672 b a' b')). Qed.
Lemma lem1979675 (b : Prop) (b' : Prop) : (term51 b b') = (term51 b b').
Proof. exact (eq_refl (term51 b b')). Qed.
Lemma lem1979676 (a' : Prop) (b : Prop) (b' : Prop) : ((term49 b b' a') = (term51 b b')) = ((term47 b a' b') = (term51 b b')).
Proof. exact (MK_COMB (@lem1979674 b a' b') (@lem1979675 b b')). Qed.
Lemma lem1979677 (a' : Prop) (b : Prop) (b' : Prop) : ((term49 b b' a') = (term50 b b')) = ((term47 b a' b') = (term51 b b')).
Proof. exact (TRANS (@lem1979671 a' b b') (@lem1979676 a' b b')). Qed.
Lemma lem1979678 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : (term47 b a' b') = (term51 b b').
Proof. exact (EQ_MP (@lem1979677 a' b b') (@lem1979668 b b' a' h1)). Qed.
Lemma lem1979679 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : (term51 b b') = (term47 b a' b').
Proof. exact (SYM (@lem1979678 b b' a' h1)). Qed.
Lemma lem1979680 (b : Prop) (b' : Prop) : (term48 b b') = (term48 b b').
Proof. exact (eq_refl (term48 b b')). Qed.
Lemma lem1979681 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : (term49 b b' a') = (term54 b b').
Proof. exact (MK_COMB (@lem1979680 b b') (@lem1979656 a' h1)). Qed.
Lemma lem1979682 (b : Prop) (b' : Prop) : (term54 b b') = (term55 b b').
Proof. exact (eq_refl (term54 b b')). Qed.
Lemma lem1979683 (b : Prop) (b' : Prop) (a' : Prop) : (term52 b b' a') = (term52 b b' a').
Proof. exact (eq_refl (term52 b b' a')). Qed.
Lemma lem1979684 (a' : Prop) (b : Prop) (b' : Prop) : ((term49 b b' a') = (term54 b b')) = ((term49 b b' a') = (term55 b b')).
Proof. exact (MK_COMB (@lem1979683 b b' a') (@lem1979682 b b')). Qed.
Lemma lem1979685 (b : Prop) (a' : Prop) (b' : Prop) : (term49 b b' a') = (term47 b a' b').
Proof. exact (eq_refl (term49 b b' a')). Qed.
Lemma lem1979686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979687 (b : Prop) (a' : Prop) (b' : Prop) : (term52 b b' a') = (term53 b a' b').
Proof. exact (MK_COMB (@lem1979686) (@lem1979685 b a' b')). Qed.
Lemma lem1979688 (b : Prop) (b' : Prop) : (term55 b b') = (term55 b b').
Proof. exact (eq_refl (term55 b b')). Qed.
Lemma lem1979689 (a' : Prop) (b : Prop) (b' : Prop) : ((term49 b b' a') = (term55 b b')) = ((term47 b a' b') = (term55 b b')).
Proof. exact (MK_COMB (@lem1979687 b a' b') (@lem1979688 b b')). Qed.
Lemma lem1979690 (a' : Prop) (b : Prop) (b' : Prop) : ((term49 b b' a') = (term54 b b')) = ((term47 b a' b') = (term55 b b')).
Proof. exact (TRANS (@lem1979684 a' b b') (@lem1979689 a' b b')). Qed.
Lemma lem1979691 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : (term47 b a' b') = (term55 b b').
Proof. exact (EQ_MP (@lem1979690 a' b b') (@lem1979681 b b' a' h1)). Qed.
Lemma lem1979692 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : (term55 b b') = (term47 b a' b').
Proof. exact (SYM (@lem1979691 b b' a' h1)). Qed.
Lemma lem1979698 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1979699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979700 : term56 = (and False).
Proof. exact (MK_COMB (@lem1979699) (@lem1979698)). Qed.
Lemma lem1979703 (b : Prop) (b' : Prop) : (b = b') = (b = b').
Proof. exact (eq_refl (b = b')). Qed.
Lemma lem1979704 (b : Prop) (b' : Prop) : (term57 b b') = (term36 b b').
Proof. exact (MK_COMB (@lem1979700) (@lem1979703 b b')). Qed.
Lemma lem1979706 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1979707 (b : Prop) (b' : Prop) : (term36 b b') = False.
Proof. exact (@lem1979706 (b = b')). Qed.
Lemma lem1979708 (b : Prop) (b' : Prop) : (term57 b b') = False.
Proof. exact (TRANS (@lem1979704 b b') (@lem1979707 b b')). Qed.
Lemma lem1979709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979710 (b : Prop) (b' : Prop) : (term58 b b') = (imp False).
Proof. exact (MK_COMB (@lem1979709) (@lem1979708 b b')). Qed.
Lemma lem1979712 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979713 (b' : Prop) : (True /\ b') = b'.
Proof. exact (@lem1979712 b'). Qed.
Lemma lem1979714 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1979715 (b' : Prop) : (term59 b') = (~ b').
Proof. exact (MK_COMB (@lem1979714) (@lem1979713 b')). Qed.
Lemma lem1979716 (b : Prop) (b' : Prop) : (term51 b b') = (term38 b').
Proof. exact (MK_COMB (@lem1979710 b b') (@lem1979715 b')). Qed.
Lemma lem1979718 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1979719 (b' : Prop) : (term38 b') = True.
Proof. exact (@lem1979718 (~ b')). Qed.
Lemma lem1979720 (b : Prop) (b' : Prop) : (term51 b b') = True.
Proof. exact (TRANS (@lem1979716 b b') (@lem1979719 b')). Qed.
Lemma lem1979721 (b : Prop) (b' : Prop) : True = (term51 b b').
Proof. exact (SYM (@lem1979720 b b')). Qed.
Lemma lem1979722 (b : Prop) (b' : Prop) : term51 b b'.
Proof. exact (EQ_MP (@lem1979721 b b') (@lem0)). Qed.
Lemma lem1979728 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1979729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979730 : term60 = (and True).
Proof. exact (MK_COMB (@lem1979729) (@lem1979728)). Qed.
Lemma lem1979733 (b : Prop) (b' : Prop) : (b = b') = (b = b').
Proof. exact (eq_refl (b = b')). Qed.
Lemma lem1979734 (b : Prop) (b' : Prop) : (term61 b b') = (term32 b b').
Proof. exact (MK_COMB (@lem1979730) (@lem1979733 b b')). Qed.
Lemma lem1979736 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979737 (b : Prop) (b' : Prop) : (term32 b b') = (b = b').
Proof. exact (@lem1979736 (b = b')). Qed.
Lemma lem1979740 (b : Prop) (b' : Prop) : (term61 b b') = (b = b').
Proof. exact (TRANS (@lem1979734 b b') (@lem1979737 b b')). Qed.
Lemma lem1979741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979742 (b : Prop) (b' : Prop) : (term62 b b') = (term34 b b').
Proof. exact (MK_COMB (@lem1979741) (@lem1979740 b b')). Qed.
Lemma lem1979744 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1979745 (b' : Prop) : (False /\ b') = False.
Proof. exact (@lem1979744 b'). Qed.
Lemma lem1979746 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1979747 (b' : Prop) : (term63 b') = (~ False).
Proof. exact (MK_COMB (@lem1979746) (@lem1979745 b')). Qed.
Lemma lem1979749 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1979750 (b' : Prop) : (term63 b') = True.
Proof. exact (TRANS (@lem1979747 b') (@lem1979749)). Qed.
Lemma lem1979751 (b : Prop) (b' : Prop) : (term55 b b') = (term64 b b').
Proof. exact (MK_COMB (@lem1979742 b b') (@lem1979750 b')). Qed.
Lemma lem1979755 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1979756 (b : Prop) (b' : Prop) : (term64 b b') = True.
Proof. exact (@lem1979755 (b = b')). Qed.
Lemma lem1979757 (b : Prop) (b' : Prop) : (term55 b b') = True.
Proof. exact (TRANS (@lem1979751 b b') (@lem1979756 b b')). Qed.
Lemma lem1979758 (b : Prop) (b' : Prop) : True = (term55 b b').
Proof. exact (SYM (@lem1979757 b b')). Qed.
Lemma lem1979759 (b : Prop) (b' : Prop) : term55 b b'.
Proof. exact (EQ_MP (@lem1979758 b b') (@lem0)). Qed.
Lemma lem1979760 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = False) : term47 b a' b'.
Proof. exact (EQ_MP (@lem1979692 b b' a' h1) (@lem1979759 b b')). Qed.
Lemma lem1979761 (b : Prop) (b' : Prop) (a' : Prop) (h1 : a' = True) : term47 b a' b'.
Proof. exact (EQ_MP (@lem1979679 b b' a' h1) (@lem1979722 b b')). Qed.
Lemma lem1979763 (b : Prop) (a' : Prop) (b' : Prop) : term47 b a' b'.
Proof. exact (or_elim (@lem1979654 a') (fun h0 : a' = True => @lem1979761 b b' a' h0) (fun h0 : a' = False => @lem1979760 b b' a' h0)). Qed.
Lemma lem1979764 (b : Prop) (a' : Prop) (b' : Prop) : term16 b a' b'.
Proof. exact (EQ_MP (@lem1979651 b a' b') (@lem1979763 b a' b')). Qed.
Lemma lem1979765 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = False) : term13 a b a' b'.
Proof. exact (EQ_MP (@lem1979479 b a' b' a h1) (@lem1979764 b a' b')). Qed.
Lemma lem1979766 (b : Prop) (a' : Prop) (b' : Prop) (a : Prop) (h1 : a = True) : term13 a b a' b'.
Proof. exact (EQ_MP (@lem1979466 b a' b' a h1) (@lem1979613 b a' b')). Qed.
Lemma lem1979769 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : term13 a b a' b'.
Proof. exact (or_elim (@lem1979435 a) (fun h0 : a = True => @lem1979766 b a' b' a h0) (fun h0 : a = False => @lem1979765 b a' b' a h0)). Qed.
Lemma lem1979770 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) (h1 : term13 a b a' b') : term13 a b a' b'.
Proof. exact (h1). Qed.
Lemma lem1979771 (a : Prop) (a' : Prop) (b : Prop) (b' : Prop) (h1 : term65 a a' b b') : term65 a a' b b'.
Proof. exact (h1). Qed.
Lemma lem1979772 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) (h1 : term65 a a' b b') (h2 : term13 a b a' b') : (a /\ b) = (a' /\ b').
Proof. exact (@lem1979770 a b a' b' h2 (@lem1979771 a a' b b' h1)). Qed.
Lemma lem1979773 (a : Prop) (a' : Prop) (b : Prop) (b' : Prop) (h1 : term65 a a' b b') : term66 a b a' b'.
Proof. exact (fun h0 : term13 a b a' b' => @lem1979772 a b a' b' h1 h0). Qed.
Lemma lem1979774 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) (h1 : term13 a b a' b') : term13 a b a' b'.
Proof. exact (h1). Qed.
Lemma lem1979775 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) (h1 : term65 a a' b b') (h2 : term13 a b a' b') : (a /\ b) = (a' /\ b').
Proof. exact (@lem1979773 a a' b b' h1 (@lem1979774 a b a' b' h2)). Qed.
Lemma lem1979776 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) (h1 : term13 a b a' b') : term13 a b a' b'.
Proof. exact (fun h0 : term65 a a' b b' => @lem1979775 a b a' b' h0 h1). Qed.
Lemma lem1979777 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : term67 a b a' b'.
Proof. exact (fun h0 : term13 a b a' b' => @lem1979776 a b a' b' h0). Qed.
Lemma lem1979781 (x : real) (y : real) (h1 : (term68 y x) = (x = y)) : (term68 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1979782 (x : real) (y : real) (h1 : (term68 y x) = (x = y)) : (x = y) = (term68 y x).
Proof. exact (SYM (@lem1979781 x y h1)). Qed.
Lemma lem1979783 (y : real) (x : real) (h1 : (x = y) = (term68 y x)) : (x = y) = (term68 y x).
Proof. exact (h1). Qed.
Lemma lem1979784 (y : real) (x : real) (h1 : (x = y) = (term68 y x)) : (term68 y x) = (x = y).
Proof. exact (SYM (@lem1979783 y x h1)). Qed.
Lemma lem1979785 (y : real) (x : real) : ((term68 y x) = (x = y)) = ((x = y) = (term68 y x)).
Proof. exact (prop_ext (fun h1 : (term68 y x) = (x = y) => @lem1979782 x y h1) (fun h1 : (x = y) = (term68 y x) => @lem1979784 y x h1)). Qed.
Lemma lem1979786 (x : real) : (term69 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1979785 y x)). Qed.
Lemma lem1979787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1979788 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1979787) (@lem1979786 x)). Qed.
Lemma lem1979789 : term73 = term74.
Proof. exact (fun_ext (fun x : real => @lem1979788 x)). Qed.
Lemma lem1979790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1979791 : term75 = term76.
Proof. exact (MK_COMB (@lem1979790) (@lem1979789)). Qed.
Lemma lem1979792 : term76.
Proof. exact (EQ_MP (@lem1979791) (@lem1339379)). Qed.
Lemma lem1979793 (x : real) : term77 x.
Proof. exact (@lem1979792 x). Qed.
Lemma lem1979794 (x : real) : (term77 x) = (term72 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1979795 (x : real) : term72 x.
Proof. exact (EQ_MP (@lem1979794 x) (@lem1979793 x)). Qed.
Lemma lem1979796 (x : real) (y : real) : term78 x y.
Proof. exact (@lem1979795 x y). Qed.
Lemma lem1979797 (y : real) (x : real) : (term78 x y) = ((x = y) = (term68 y x)).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1979799 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term1 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1979807 (y : real) (x : real) : (x = y) = (term68 y x).
Proof. exact (EQ_MP (@lem1979797 y x) (@lem1979796 x y)). Qed.
Lemma lem1979808 (x2 : real) (y2 : real) (x1 : real) (y1 : real) : ((real_div x1 y1) = (real_div x2 y2)) = (term79 x2 y2 x1 y1).
Proof. exact (@lem1979807 (real_div x2 y2) (real_div x1 y1)). Qed.
Lemma lem1979811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979812 (x2 : real) (y2 : real) (x1 : real) (y1 : real) : (term80 x1 y1 x2 y2) = (term81 x2 y2 x1 y1).
Proof. exact (MK_COMB (@lem1979811) (@lem1979808 x2 y2 x1 y1)). Qed.
Lemma lem1979816 (y : real) (x : real) : (x = y) = (term68 y x).
Proof. exact (EQ_MP (@lem1979797 y x) (@lem1979796 x y)). Qed.
Lemma lem1979817 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((real_mul x1 y2) = (real_mul x2 y1)) = (term82 x2 y1 x1 y2).
Proof. exact (@lem1979816 (real_mul x2 y1) (real_mul x1 y2)). Qed.
Lemma lem1979820 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (((real_div x1 y1) = (real_div x2 y2)) = ((real_mul x1 y2) = (real_mul x2 y1))) = ((term79 x2 y2 x1 y1) = (term82 x2 y1 x1 y2)).
Proof. exact (MK_COMB (@lem1979812 x2 y2 x1 y1) (@lem1979817 x2 y1 x1 y2)). Qed.
Lemma lem1979825 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : ((term79 x2 y2 x1 y1) = (term82 x2 y1 x1 y2)) = (((real_div x1 y1) = (real_div x2 y2)) = ((real_mul x1 y2) = (real_mul x2 y1))).
Proof. exact (SYM (@lem1979820 x2 y1 x1 y2)). Qed.
Lemma lem1979827 (a : Prop) (b : Prop) (a' : Prop) (b' : Prop) : term13 a b a' b'.
Proof. exact (@lem1979777 a b a' b' (@lem1979769 a b a' b')). Qed.
Lemma lem1979828 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term83 x2 y1 x1 y2.
Proof. exact (@lem1979827 (term2 x1 y1 x2 y2) (term2 x2 y2 x1 y1) (term3 x1 y2 x2 y1) (term3 x2 y1 x1 y2)). Qed.
Lemma lem1979830 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term0 x1 y2 x2 y1.
Proof. exact (@lem1979415 x1 y2 x2 y1 (@lem1979407 x1 y2 x2 y1)). Qed.
Lemma lem1979832 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term0 x1 y2 x2 y1.
Proof. exact (@lem1979415 x1 y2 x2 y1 (@lem1979407 x1 y2 x2 y1)). Qed.
Lemma lem1979833 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term0 x2 y1 x1 y2.
Proof. exact (@lem1979832 x2 y1 x1 y2). Qed.
Lemma lem1979834 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term84 y2.
Proof. exact (proj2 (@lem1979799 y1 y2 h1)). Qed.
Lemma lem1979835 (y2 : real) : (term84 y2) = ((term84 y2) = True).
Proof. exact (@lem7 (term84 y2)). Qed.
Lemma lem1979837 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term84 y1.
Proof. exact (proj1 (@lem1979799 y1 y2 h1)). Qed.
Lemma lem1979838 (y1 : real) : (term84 y1) = ((term84 y1) = True).
Proof. exact (@lem7 (term84 y1)). Qed.
Lemma lem1979843 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term84 y1) = True.
Proof. exact (EQ_MP (@lem1979838 y1) (@lem1979837 y1 y2 h1)). Qed.
Lemma lem1979844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979845 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term85 y1) = (and True).
Proof. exact (MK_COMB (@lem1979844) (@lem1979843 y1 y2 h1)). Qed.
Lemma lem1979847 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term84 y2) = True.
Proof. exact (EQ_MP (@lem1979835 y2) (@lem1979834 y1 y2 h1)). Qed.
Lemma lem1979848 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term1 y1 y2) = (True /\ True).
Proof. exact (MK_COMB (@lem1979845 y1 y2 h1) (@lem1979847 y1 y2 h1)). Qed.
Lemma lem1979850 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979851 : (True /\ True) = True.
Proof. exact (@lem1979850 True). Qed.
Lemma lem1979852 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term1 y1 y2) = True.
Proof. exact (TRANS (@lem1979848 y1 y2 h1) (@lem1979851)). Qed.
Lemma lem1979853 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : True = (term1 y1 y2).
Proof. exact (SYM (@lem1979852 y1 y2 h1)). Qed.
Lemma lem1979854 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term1 y1 y2.
Proof. exact (EQ_MP (@lem1979853 y1 y2 h1) (@lem0)). Qed.
Lemma lem1979855 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term84 y2.
Proof. exact (proj2 (@lem1979799 y1 y2 h1)). Qed.
Lemma lem1979856 (y2 : real) : (term84 y2) = ((term84 y2) = True).
Proof. exact (@lem7 (term84 y2)). Qed.
Lemma lem1979858 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term84 y1.
Proof. exact (proj1 (@lem1979799 y1 y2 h1)). Qed.
Lemma lem1979859 (y1 : real) : (term84 y1) = ((term84 y1) = True).
Proof. exact (@lem7 (term84 y1)). Qed.
Lemma lem1979864 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term84 y2) = True.
Proof. exact (EQ_MP (@lem1979856 y2) (@lem1979855 y1 y2 h1)). Qed.
Lemma lem1979865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979866 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term85 y2) = (and True).
Proof. exact (MK_COMB (@lem1979865) (@lem1979864 y1 y2 h1)). Qed.
Lemma lem1979868 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term84 y1) = True.
Proof. exact (EQ_MP (@lem1979859 y1) (@lem1979858 y1 y2 h1)). Qed.
Lemma lem1979869 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term1 y2 y1) = (True /\ True).
Proof. exact (MK_COMB (@lem1979866 y1 y2 h1) (@lem1979868 y1 y2 h1)). Qed.
Lemma lem1979871 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979872 : (True /\ True) = True.
Proof. exact (@lem1979871 True). Qed.
Lemma lem1979873 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term1 y2 y1) = True.
Proof. exact (TRANS (@lem1979869 y1 y2 h1) (@lem1979872)). Qed.
Lemma lem1979874 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : True = (term1 y2 y1).
Proof. exact (SYM (@lem1979873 y1 y2 h1)). Qed.
Lemma lem1979875 (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term1 y2 y1.
Proof. exact (EQ_MP (@lem1979874 y1 y2 h1) (@lem0)). Qed.
Lemma lem1979876 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term2 x2 y2 x1 y1) = (term3 x2 y1 x1 y2).
Proof. exact (@lem1979833 x2 y1 x1 y2 (@lem1979875 y1 y2 h1)). Qed.
Lemma lem1979877 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term2 x1 y1 x2 y2) = (term3 x1 y2 x2 y1).
Proof. exact (@lem1979830 x1 y2 x2 y1 (@lem1979854 y1 y2 h1)). Qed.
Lemma lem1979878 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term1 y1 y2) : term86 x2 y1 x1 y2.
Proof. exact (conj (@lem1979877 x1 x2 y1 y2 h1) (@lem1979876 x2 x1 y1 y2 h1)). Qed.
Lemma lem1979879 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term1 y1 y2) : (term79 x2 y2 x1 y1) = (term82 x2 y1 x1 y2).
Proof. exact (@lem1979828 x2 y1 x1 y2 (@lem1979878 x2 x1 y1 y2 h1)). Qed.
Lemma lem1979880 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term1 y1 y2) : ((real_div x1 y1) = (real_div x2 y2)) = ((real_mul x1 y2) = (real_mul x2 y1)).
Proof. exact (EQ_MP (@lem1979825 x1 y2 x2 y1) (@lem1979879 x2 x1 y1 y2 h1)). Qed.
