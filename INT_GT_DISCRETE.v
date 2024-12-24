Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_GT_DISCRETE_term_abbrevs.
Require Import INT_LT_DISCRETE_spec.
Require Import int_ge_spec.
Require Import int_gt_spec.
Require Import int_le_spec.
Require Import int_lt_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Lemma lem2299450 (x : int) (y : int) (h1 : (int_lt x y) = (term0 x y)) : (int_lt x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299451 (x : int) (y : int) (h1 : (int_lt x y) = (term0 x y)) : (term0 x y) = (int_lt x y).
Proof. exact (SYM (@lem2299450 x y h1)). Qed.
Lemma lem2299452 (x : int) (y : int) (h1 : (term0 x y) = (int_lt x y)) : (term0 x y) = (int_lt x y).
Proof. exact (h1). Qed.
Lemma lem2299453 (x : int) (y : int) (h1 : (term0 x y) = (int_lt x y)) : (int_lt x y) = (term0 x y).
Proof. exact (SYM (@lem2299452 x y h1)). Qed.
Lemma lem2299454 (x : int) (y : int) : ((int_lt x y) = (term0 x y)) = ((term0 x y) = (int_lt x y)).
Proof. exact (prop_ext (fun h1 : (int_lt x y) = (term0 x y) => @lem2299451 x y h1) (fun h1 : (term0 x y) = (int_lt x y) => @lem2299453 x y h1)). Qed.
Lemma lem2299455 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2299454 x y)). Qed.
Lemma lem2299456 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299457 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2299456) (@lem2299455 x)). Qed.
Lemma lem2299458 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2299457 x)). Qed.
Lemma lem2299459 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299460 : term7 = term8.
Proof. exact (MK_COMB (@lem2299459) (@lem2299458)). Qed.
Lemma lem2299461 : term8.
Proof. exact (EQ_MP (@lem2299460) (@lem2269769)). Qed.
Lemma lem2299464 (x : int) (y : int) (h1 : (int_le x y) = (term9 x y)) : (int_le x y) = (term9 x y).
Proof. exact (h1). Qed.
Lemma lem2299465 (x : int) (y : int) (h1 : (int_le x y) = (term9 x y)) : (term9 x y) = (int_le x y).
Proof. exact (SYM (@lem2299464 x y h1)). Qed.
Lemma lem2299466 (x : int) (y : int) (h1 : (term9 x y) = (int_le x y)) : (term9 x y) = (int_le x y).
Proof. exact (h1). Qed.
Lemma lem2299467 (x : int) (y : int) (h1 : (term9 x y) = (int_le x y)) : (int_le x y) = (term9 x y).
Proof. exact (SYM (@lem2299466 x y h1)). Qed.
Lemma lem2299468 (x : int) (y : int) : ((int_le x y) = (term9 x y)) = ((term9 x y) = (int_le x y)).
Proof. exact (prop_ext (fun h1 : (int_le x y) = (term9 x y) => @lem2299465 x y h1) (fun h1 : (term9 x y) = (int_le x y) => @lem2299467 x y h1)). Qed.
Lemma lem2299469 (x : int) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : int => @lem2299468 x y)). Qed.
Lemma lem2299470 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299471 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2299470) (@lem2299469 x)). Qed.
Lemma lem2299472 : term14 = term15.
Proof. exact (fun_ext (fun x : int => @lem2299471 x)). Qed.
Lemma lem2299473 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299474 : term16 = term17.
Proof. exact (MK_COMB (@lem2299473) (@lem2299472)). Qed.
Lemma lem2299475 : term17.
Proof. exact (EQ_MP (@lem2299474) (@lem2269094)). Qed.
Lemma lem2299476 (x : int) : term18 x.
Proof. exact (@lem2299461 x). Qed.
Lemma lem2299477 (x : int) : (term18 x) = (term4 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2299478 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2299477 x) (@lem2299476 x)). Qed.
Lemma lem2299479 (x : int) (y : int) : term19 x y.
Proof. exact (@lem2299478 x y). Qed.
Lemma lem2299480 (x : int) (y : int) : (term19 x y) = ((term0 x y) = (int_lt x y)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem2299482 (x : int) : term20 x.
Proof. exact (@lem2299475 x). Qed.
Lemma lem2299483 (x : int) : (term20 x) = (term13 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2299484 (x : int) : term13 x.
Proof. exact (EQ_MP (@lem2299483 x) (@lem2299482 x)). Qed.
Lemma lem2299485 (x : int) (y : int) : term21 x y.
Proof. exact (@lem2299484 x y). Qed.
Lemma lem2299486 (x : int) (y : int) : (term21 x y) = ((term9 x y) = (int_le x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem2299488 (y : real) : term22 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem2299489 (y : real) : (term22 y) = (term23 y).
Proof. exact (eq_refl (term22 y)). Qed.
Lemma lem2299490 (y : real) : term23 y.
Proof. exact (EQ_MP (@lem2299489 y) (@lem2299488 y)). Qed.
Lemma lem2299491 (y : real) (x : real) : term24 y x.
Proof. exact (@lem2299490 y x). Qed.
Lemma lem2299492 (y : real) (x : real) : (term24 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term24 y x)). Qed.
Lemma lem2299494 (y : real) : term25 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem2299495 (y : real) : (term25 y) = (term26 y).
Proof. exact (eq_refl (term25 y)). Qed.
Lemma lem2299496 (y : real) : term26 y.
Proof. exact (EQ_MP (@lem2299495 y) (@lem2299494 y)). Qed.
Lemma lem2299497 (y : real) (x : real) : term27 y x.
Proof. exact (@lem2299496 y x). Qed.
Lemma lem2299498 (y : real) (x : real) : (term27 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term27 y x)). Qed.
Lemma lem2299500 (x : int) : term28 x.
Proof. exact (@lem2270452 x). Qed.
Lemma lem2299501 (x : int) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2299502 (x : int) : term29 x.
Proof. exact (EQ_MP (@lem2299501 x) (@lem2299500 x)). Qed.
Lemma lem2299503 (x : int) (y : int) : term30 x y.
Proof. exact (@lem2299502 x y). Qed.
Lemma lem2299504 (x : int) (y : int) : (term30 x y) = ((int_ge x y) = (term31 x y)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem2299506 (x : int) : term32 x.
Proof. exact (@lem2271143 x). Qed.
Lemma lem2299507 (x : int) : (term32 x) = (term33 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem2299508 (x : int) : term33 x.
Proof. exact (EQ_MP (@lem2299507 x) (@lem2299506 x)). Qed.
Lemma lem2299509 (x : int) (y : int) : term34 x y.
Proof. exact (@lem2299508 x y). Qed.
Lemma lem2299510 (x : int) (y : int) : (term34 x y) = ((int_gt x y) = (term35 x y)).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem2299523 (x : int) (y : int) : (int_gt x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2299510 x y) (@lem2299509 x y)). Qed.
Lemma lem2299525 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem2299492 y x) (@lem2299491 y x)). Qed.
Lemma lem2299526 (y : int) (x : int) : (term35 x y) = (term0 y x).
Proof. exact (@lem2299525 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2299528 (x : int) (y : int) : (term0 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299480 x y) (@lem2299479 x y)). Qed.
Lemma lem2299529 (y : int) (x : int) : (term0 y x) = (int_lt y x).
Proof. exact (@lem2299528 y x). Qed.
Lemma lem2299530 (y : int) (x : int) : (term35 x y) = (int_lt y x).
Proof. exact (TRANS (@lem2299526 y x) (@lem2299529 y x)). Qed.
Lemma lem2299531 (y : int) (x : int) : (int_gt x y) = (int_lt y x).
Proof. exact (TRANS (@lem2299523 x y) (@lem2299530 y x)). Qed.
Lemma lem2299532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2299533 (y : int) (x : int) : (term36 x y) = (term37 y x).
Proof. exact (MK_COMB (@lem2299532) (@lem2299531 y x)). Qed.
Lemma lem2299535 (x : int) (y : int) : (int_ge x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2299504 x y) (@lem2299503 x y)). Qed.
Lemma lem2299536 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (@lem2299535 x (term40 y)). Qed.
Lemma lem2299538 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem2299498 y x) (@lem2299497 y x)). Qed.
Lemma lem2299539 (y : int) (x : int) : (term39 x y) = (term41 y x).
Proof. exact (@lem2299538 (term42 y) (real_of_int x)). Qed.
Lemma lem2299541 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299486 x y) (@lem2299485 x y)). Qed.
Lemma lem2299542 (y : int) (x : int) : (term41 y x) = (term43 y x).
Proof. exact (@lem2299541 (term40 y) x). Qed.
Lemma lem2299543 (y : int) (x : int) : (term39 x y) = (term43 y x).
Proof. exact (TRANS (@lem2299539 y x) (@lem2299542 y x)). Qed.
Lemma lem2299544 (y : int) (x : int) : (term38 x y) = (term43 y x).
Proof. exact (TRANS (@lem2299536 x y) (@lem2299543 y x)). Qed.
Lemma lem2299545 (y : int) (x : int) : ((int_gt x y) = (term38 x y)) = ((int_lt y x) = (term43 y x)).
Proof. exact (MK_COMB (@lem2299533 y x) (@lem2299544 y x)). Qed.
Lemma lem2299548 (x : int) : (term44 x) = (term45 x).
Proof. exact (fun_ext (fun y : int => @lem2299545 y x)). Qed.
Lemma lem2299549 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299550 (x : int) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem2299549) (@lem2299548 x)). Qed.
Lemma lem2299555 : term48 = term49.
Proof. exact (fun_ext (fun x : int => @lem2299550 x)). Qed.
Lemma lem2299556 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299557 : term50 = term51.
Proof. exact (MK_COMB (@lem2299556) (@lem2299555)). Qed.
Lemma lem2299562 : term51 = term50.
Proof. exact (SYM (@lem2299557)). Qed.
Lemma lem2299563 (x : int) : term52 x.
Proof. exact (@lem2299447 x). Qed.
Lemma lem2299564 (x : int) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem2299565 (x : int) : term53 x.
Proof. exact (EQ_MP (@lem2299564 x) (@lem2299563 x)). Qed.
Lemma lem2299566 (x : int) (y : int) : term54 x y.
Proof. exact (@lem2299565 x y). Qed.
Lemma lem2299567 (x : int) (y : int) : (term54 x y) = ((int_lt x y) = (term43 x y)).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem2299570 (x : int) (y : int) : (int_lt x y) = (term43 x y).
Proof. exact (EQ_MP (@lem2299567 x y) (@lem2299566 x y)). Qed.
Lemma lem2299571 (y : int) (x : int) : (int_lt y x) = (term43 y x).
Proof. exact (@lem2299570 y x). Qed.
Lemma lem2299576 (x : int) : term47 x.
Proof. exact (fun y : int => @lem2299571 y x). Qed.
Lemma lem2299581 : term51.
Proof. exact (fun x : int => @lem2299576 x). Qed.
Lemma lem2299582 : term50.
Proof. exact (EQ_MP (@lem2299562) (@lem2299581)). Qed.
