Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RMUL_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1602380 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (term0 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1602381 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (real_lt y x) = (term0 x y).
Proof. exact (SYM (@lem1602380 y x h1)). Qed.
Lemma lem1602382 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (real_lt y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1602383 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (term0 x y) = (real_lt y x).
Proof. exact (SYM (@lem1602382 x y h1)). Qed.
Lemma lem1602384 (x : real) (y : real) : ((term0 x y) = (real_lt y x)) = ((real_lt y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_lt y x) => @lem1602381 y x h1) (fun h1 : (real_lt y x) = (term0 x y) => @lem1602383 x y h1)). Qed.
Lemma lem1602385 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1602384 x y)). Qed.
Lemma lem1602386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602387 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1602386) (@lem1602385 x)). Qed.
Lemma lem1602388 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1602387 x)). Qed.
Lemma lem1602389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602390 : term7 = term8.
Proof. exact (MK_COMB (@lem1602389) (@lem1602388)). Qed.
Lemma lem1602391 : term8.
Proof. exact (EQ_MP (@lem1602390) (@lem1495933)). Qed.
Lemma lem1602392 (x : real) : term9 x.
Proof. exact (@lem1600741 x). Qed.
Lemma lem1602393 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1602394 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1602393 x) (@lem1602392 x)). Qed.
Lemma lem1602395 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1602394 x y). Qed.
Lemma lem1602396 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1602397 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1602396 x y) (@lem1602395 x y)). Qed.
Lemma lem1602398 (x : real) (y : real) (z : real) : term13 x y z.
Proof. exact (@lem1602397 x y z). Qed.
Lemma lem1602399 (z : real) (x : real) (y : real) : (term13 x y z) = (term14 z x y).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1602400 (z : real) (x : real) (y : real) : term14 z x y.
Proof. exact (EQ_MP (@lem1602399 z x y) (@lem1602398 x y z)). Qed.
Lemma lem1602401 (z : real) (h1 : term15 z) : term15 z.
Proof. exact (h1). Qed.
Lemma lem1602402 (x : real) (y : real) (z : real) (h1 : term15 z) : (term16 x y z) = (real_le x y).
Proof. exact (@lem1602400 z x y (@lem1602401 z h1)). Qed.
Lemma lem1602408 (x : real) : term17 x.
Proof. exact (@lem1602391 x). Qed.
Lemma lem1602409 (x : real) : (term17 x) = (term4 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1602410 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1602409 x) (@lem1602408 x)). Qed.
Lemma lem1602411 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1602410 x y). Qed.
Lemma lem1602412 (x : real) (y : real) : (term18 x y) = ((real_lt y x) = (term0 x y)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1602429 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1602430 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem1602429 p q p' q'). Qed.
Lemma lem1602431 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem1602430 p q p'). Qed.
Lemma lem1602432 (z : real) (x : real) (y : real) : term22 z x y.
Proof. exact (@lem1602431 (term15 z) ((term23 x y z) = (real_lt x y))). Qed.
Lemma lem1602433 (z : real) (x : real) (y : real) (p' : Prop) : term24 z x y p'.
Proof. exact (@lem1602432 z x y p'). Qed.
Lemma lem1602434 (z : real) (x : real) (y : real) (p' : Prop) : (term24 z x y p') = (term25 z x y p').
Proof. exact (eq_refl (term24 z x y p')). Qed.
Lemma lem1602435 (z : real) (x : real) (y : real) (p' : Prop) : term25 z x y p'.
Proof. exact (EQ_MP (@lem1602434 z x y p') (@lem1602433 z x y p')). Qed.
Lemma lem1602436 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term26 z x y p' q'.
Proof. exact (@lem1602435 z x y p' q'). Qed.
Lemma lem1602437 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term26 z x y p' q') = (term27 z x y p' q').
Proof. exact (eq_refl (term26 z x y p' q')). Qed.
Lemma lem1602438 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term27 z x y p' q'.
Proof. exact (EQ_MP (@lem1602437 z x y p' q') (@lem1602436 z x y p' q')). Qed.
Lemma lem1602440 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602412 x y) (@lem1602411 x y)). Qed.
Lemma lem1602441 (z : real) : (term15 z) = (term28 z).
Proof. exact (@lem1602440 z term29). Qed.
Lemma lem1602442 (x : real) (y : real) (z : real) (q' : Prop) : term30 x y z q'.
Proof. exact (@lem1602438 z x y (term28 z) q'). Qed.
Lemma lem1602443 (x : real) (y : real) (z : real) (q' : Prop) : term31 x y z q'.
Proof. exact (@lem1602442 x y z q' (@lem1602441 z)). Qed.
Lemma lem1602444 (z : real) (h1 : term28 z) : term28 z.
Proof. exact (h1). Qed.
Lemma lem1602445 (z : real) : term32 z.
Proof. exact (@lem82 (term33 z)). Qed.
Lemma lem1602450 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602412 x y) (@lem1602411 x y)). Qed.
Lemma lem1602451 (y : real) (x : real) (z : real) : (term23 x y z) = (term34 y x z).
Proof. exact (@lem1602450 (real_mul y z) (real_mul x z)). Qed.
Lemma lem1602453 (z : real) (x : real) (y : real) : term14 z x y.
Proof. exact (fun h0 : term15 z => @lem1602402 x y z h0). Qed.
Lemma lem1602454 (z : real) (y : real) (x : real) : term14 z y x.
Proof. exact (@lem1602453 z y x). Qed.
Lemma lem1602456 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602412 x y) (@lem1602411 x y)). Qed.
Lemma lem1602457 (z : real) : (term15 z) = (term28 z).
Proof. exact (@lem1602456 z term29). Qed.
Lemma lem1602459 (z : real) (h1 : term28 z) : (term33 z) = False.
Proof. exact (@lem1602445 z (@lem1602444 z h1)). Qed.
Lemma lem1602460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602461 (z : real) (h1 : term28 z) : (term28 z) = (~ False).
Proof. exact (MK_COMB (@lem1602460) (@lem1602459 z h1)). Qed.
Lemma lem1602463 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1602464 (z : real) (h1 : term28 z) : (term28 z) = True.
Proof. exact (TRANS (@lem1602461 z h1) (@lem1602463)). Qed.
Lemma lem1602465 (z : real) (h1 : term28 z) : (term15 z) = True.
Proof. exact (TRANS (@lem1602457 z) (@lem1602464 z h1)). Qed.
Lemma lem1602466 (z : real) (h1 : term28 z) : True = (term15 z).
Proof. exact (SYM (@lem1602465 z h1)). Qed.
Lemma lem1602467 (z : real) (h1 : term28 z) : term15 z.
Proof. exact (EQ_MP (@lem1602466 z h1) (@lem0)). Qed.
Lemma lem1602468 (y : real) (x : real) (z : real) (h1 : term28 z) : (term16 y x z) = (real_le y x).
Proof. exact (@lem1602454 z y x (@lem1602467 z h1)). Qed.
Lemma lem1602469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602470 (y : real) (x : real) (z : real) (h1 : term28 z) : (term34 y x z) = (term0 y x).
Proof. exact (MK_COMB (@lem1602469) (@lem1602468 y x z h1)). Qed.
Lemma lem1602471 (y : real) (x : real) (z : real) (h1 : term28 z) : (term23 x y z) = (term0 y x).
Proof. exact (TRANS (@lem1602451 y x z) (@lem1602470 y x z h1)). Qed.
Lemma lem1602472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1602473 (y : real) (x : real) (z : real) (h1 : term28 z) : (term35 x y z) = (term36 y x).
Proof. exact (MK_COMB (@lem1602472) (@lem1602471 y x z h1)). Qed.
Lemma lem1602475 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1602412 x y) (@lem1602411 x y)). Qed.
Lemma lem1602476 (y : real) (x : real) : (real_lt x y) = (term0 y x).
Proof. exact (@lem1602475 y x). Qed.
Lemma lem1602477 (y : real) (x : real) (z : real) (h1 : term28 z) : ((term23 x y z) = (real_lt x y)) = ((term0 y x) = (term0 y x)).
Proof. exact (MK_COMB (@lem1602473 y x z h1) (@lem1602476 y x)). Qed.
Lemma lem1602479 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1602480 (x : Prop) : (x = x) = True.
Proof. exact (@lem1602479 Prop x). Qed.
Lemma lem1602481 (y : real) (x : real) : ((term0 y x) = (term0 y x)) = True.
Proof. exact (@lem1602480 (term0 y x)). Qed.
Lemma lem1602482 (x : real) (y : real) (z : real) (h1 : term28 z) : ((term23 x y z) = (real_lt x y)) = True.
Proof. exact (TRANS (@lem1602477 y x z h1) (@lem1602481 y x)). Qed.
Lemma lem1602483 (z : real) (x : real) (y : real) : term37 z x y.
Proof. exact (fun h0 : term28 z => @lem1602482 x y z h0). Qed.
Lemma lem1602484 (x : real) (y : real) (z : real) : term38 x y z.
Proof. exact (@lem1602443 x y z True). Qed.
Lemma lem1602485 (x : real) (y : real) (z : real) : (term39 z x y) = (term40 z).
Proof. exact (@lem1602484 x y z (@lem1602483 z x y)). Qed.
Lemma lem1602487 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1602488 (z : real) : (term40 z) = True.
Proof. exact (@lem1602487 (term28 z)). Qed.
Lemma lem1602489 (z : real) (x : real) (y : real) : (term39 z x y) = True.
Proof. exact (TRANS (@lem1602485 x y z) (@lem1602488 z)). Qed.
Lemma lem1602490 (x : real) (y : real) : (term41 x y) = term42.
Proof. exact (fun_ext (fun z : real => @lem1602489 z x y)). Qed.
Lemma lem1602491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602492 (x : real) (y : real) : (term43 x y) = term44.
Proof. exact (MK_COMB (@lem1602491) (@lem1602490 x y)). Qed.
Lemma lem1602494 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1602495 (t : Prop) : (term46 t) = t.
Proof. exact (@lem1602494 real t). Qed.
Lemma lem1602496 : term44 = True.
Proof. exact (@lem1602495 True). Qed.
Lemma lem1602497 (x : real) (y : real) : (term43 x y) = True.
Proof. exact (TRANS (@lem1602492 x y) (@lem1602496)). Qed.
Lemma lem1602498 (x : real) : (term47 x) = term42.
Proof. exact (fun_ext (fun y : real => @lem1602497 x y)). Qed.
Lemma lem1602499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602500 (x : real) : (term48 x) = term44.
Proof. exact (MK_COMB (@lem1602499) (@lem1602498 x)). Qed.
Lemma lem1602502 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1602503 (t : Prop) : (term46 t) = t.
Proof. exact (@lem1602502 real t). Qed.
Lemma lem1602504 : term44 = True.
Proof. exact (@lem1602503 True). Qed.
Lemma lem1602505 (x : real) : (term48 x) = True.
Proof. exact (TRANS (@lem1602500 x) (@lem1602504)). Qed.
Lemma lem1602506 : term49 = term42.
Proof. exact (fun_ext (fun x : real => @lem1602505 x)). Qed.
Lemma lem1602507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602508 : term50 = term44.
Proof. exact (MK_COMB (@lem1602507) (@lem1602506)). Qed.
Lemma lem1602510 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1602511 (t : Prop) : (term46 t) = t.
Proof. exact (@lem1602510 real t). Qed.
Lemma lem1602512 : term44 = True.
Proof. exact (@lem1602511 True). Qed.
Lemma lem1602513 : term50 = True.
Proof. exact (TRANS (@lem1602508) (@lem1602512)). Qed.
Lemma lem1602514 : True = term50.
Proof. exact (SYM (@lem1602513)). Qed.
Lemma lem1602515 : term50.
Proof. exact (EQ_MP (@lem1602514) (@lem0)). Qed.
