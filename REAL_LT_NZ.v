Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_NZ_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LT_LE_spec.
Require Import REAL_POS_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1384344 (n : nat) : term0 n.
Proof. exact (@lem9784 ((real_of_num n) = term1)). Qed.
Lemma lem1384345 (n : nat) : (term0 n) = (term2 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1384346 (n : nat) : term2 n.
Proof. exact (EQ_MP (@lem1384345 n) (@lem1384344 n)). Qed.
Lemma lem1384348 (n : nat) (h1 : term3 n) : term3 n.
Proof. exact (h1). Qed.
Lemma lem1384349 (x : real) : term4 x.
Proof. exact (@lem1379381 x). Qed.
Lemma lem1384350 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1384351 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1384350 x) (@lem1384349 x)). Qed.
Lemma lem1384352 (x : real) (y : real) : term6 x y.
Proof. exact (@lem1384351 x y). Qed.
Lemma lem1384353 (x : real) (y : real) : (term6 x y) = ((real_lt x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1384360 (x : real) (y : real) : (real_lt x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1384353 x y) (@lem1384352 x y)). Qed.
Lemma lem1384361 (n : nat) : (term8 n) = (term9 n).
Proof. exact (@lem1384360 term1 (real_of_num n)). Qed.
Lemma lem1384366 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1384367 (n : nat) : ((term3 n) = (term8 n)) = ((term3 n) = (term9 n)).
Proof. exact (MK_COMB (@lem1384366 n) (@lem1384361 n)). Qed.
Lemma lem1384370 (n : nat) : ((term3 n) = (term9 n)) = ((term3 n) = (term8 n)).
Proof. exact (SYM (@lem1384367 n)). Qed.
Lemma lem1384374 (n : nat) (h1 : term1 = (real_of_num n)) : term1 = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem1384375 (n : nat) (h1 : term1 = (real_of_num n)) : (real_of_num n) = term1.
Proof. exact (SYM (@lem1384374 n h1)). Qed.
Lemma lem1384376 (n : nat) (h1 : (real_of_num n) = term1) : (real_of_num n) = term1.
Proof. exact (h1). Qed.
Lemma lem1384377 (n : nat) (h1 : (real_of_num n) = term1) : term1 = (real_of_num n).
Proof. exact (SYM (@lem1384376 n h1)). Qed.
Lemma lem1384378 (n : nat) : (term1 = (real_of_num n)) = ((real_of_num n) = term1).
Proof. exact (prop_ext (fun h1 : term1 = (real_of_num n) => @lem1384375 n h1) (fun h1 : (real_of_num n) = term1 => @lem1384377 n h1)). Qed.
Lemma lem1384379 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384380 (n : nat) : (term11 n) = (term3 n).
Proof. exact (MK_COMB (@lem1384379) (@lem1384378 n)). Qed.
Lemma lem1384381 (n : nat) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1384382 (n : nat) : (term9 n) = (term13 n).
Proof. exact (MK_COMB (@lem1384381 n) (@lem1384380 n)). Qed.
Lemma lem1384383 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1384384 (n : nat) : ((term3 n) = (term9 n)) = ((term3 n) = (term13 n)).
Proof. exact (MK_COMB (@lem1384383 n) (@lem1384382 n)). Qed.
Lemma lem1384385 (n : nat) : ((term3 n) = (term13 n)) = ((term3 n) = (term9 n)).
Proof. exact (SYM (@lem1384384 n)). Qed.
Lemma lem1384386 (n : nat) : term14 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1384387 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem1384388 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem1384387 n) (@lem1384386 n)). Qed.
Lemma lem1384389 (n : nat) : (term15 n) = ((term15 n) = True).
Proof. exact (@lem7 (term15 n)). Qed.
Lemma lem1384401 (n : nat) (h1 : (real_of_num n) = term1) : (real_of_num n) = term1.
Proof. exact (h1). Qed.
Lemma lem1384402 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1384403 (n : nat) (h1 : (real_of_num n) = term1) : (term16 n) = term17.
Proof. exact (MK_COMB (@lem1384402) (@lem1384401 n h1)). Qed.
Lemma lem1384404 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1384405 (n : nat) (h1 : (real_of_num n) = term1) : ((real_of_num n) = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem1384403 n h1) (@lem1384404)). Qed.
Lemma lem1384407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384408 (x : real) : (x = x) = True.
Proof. exact (@lem1384407 real x). Qed.
Lemma lem1384409 : (term1 = term1) = True.
Proof. exact (@lem1384408 term1). Qed.
Lemma lem1384410 (n : nat) (h1 : (real_of_num n) = term1) : ((real_of_num n) = term1) = True.
Proof. exact (TRANS (@lem1384405 n h1) (@lem1384409)). Qed.
Lemma lem1384411 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384412 (n : nat) (h1 : (real_of_num n) = term1) : (term3 n) = (~ True).
Proof. exact (MK_COMB (@lem1384411) (@lem1384410 n h1)). Qed.
Lemma lem1384414 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1384415 (n : nat) (h1 : (real_of_num n) = term1) : (term3 n) = False.
Proof. exact (TRANS (@lem1384412 n h1) (@lem1384414)). Qed.
Lemma lem1384416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1384417 (n : nat) (h1 : (real_of_num n) = term1) : (term10 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1384416) (@lem1384415 n h1)). Qed.
Lemma lem1384421 (n : nat) : (term15 n) = True.
Proof. exact (EQ_MP (@lem1384389 n) (@lem1384388 n)). Qed.
Lemma lem1384422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384423 (n : nat) : (term12 n) = (and True).
Proof. exact (MK_COMB (@lem1384422) (@lem1384421 n)). Qed.
Lemma lem1384427 (n : nat) (h1 : (real_of_num n) = term1) : (real_of_num n) = term1.
Proof. exact (h1). Qed.
Lemma lem1384428 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1384429 (n : nat) (h1 : (real_of_num n) = term1) : (term16 n) = term17.
Proof. exact (MK_COMB (@lem1384428) (@lem1384427 n h1)). Qed.
Lemma lem1384430 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1384431 (n : nat) (h1 : (real_of_num n) = term1) : ((real_of_num n) = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem1384429 n h1) (@lem1384430)). Qed.
Lemma lem1384433 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384434 (x : real) : (x = x) = True.
Proof. exact (@lem1384433 real x). Qed.
Lemma lem1384435 : (term1 = term1) = True.
Proof. exact (@lem1384434 term1). Qed.
Lemma lem1384436 (n : nat) (h1 : (real_of_num n) = term1) : ((real_of_num n) = term1) = True.
Proof. exact (TRANS (@lem1384431 n h1) (@lem1384435)). Qed.
Lemma lem1384437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384438 (n : nat) (h1 : (real_of_num n) = term1) : (term3 n) = (~ True).
Proof. exact (MK_COMB (@lem1384437) (@lem1384436 n h1)). Qed.
Lemma lem1384440 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1384441 (n : nat) (h1 : (real_of_num n) = term1) : (term3 n) = False.
Proof. exact (TRANS (@lem1384438 n h1) (@lem1384440)). Qed.
Lemma lem1384442 (n : nat) (h1 : (real_of_num n) = term1) : (term13 n) = (True /\ False).
Proof. exact (MK_COMB (@lem1384423 n) (@lem1384441 n h1)). Qed.
Lemma lem1384444 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384445 : (True /\ False) = False.
Proof. exact (@lem1384444 False). Qed.
Lemma lem1384446 (n : nat) (h1 : (real_of_num n) = term1) : (term13 n) = False.
Proof. exact (TRANS (@lem1384442 n h1) (@lem1384445)). Qed.
Lemma lem1384447 (n : nat) (h1 : (real_of_num n) = term1) : ((term3 n) = (term13 n)) = (False = False).
Proof. exact (MK_COMB (@lem1384417 n h1) (@lem1384446 n h1)). Qed.
Lemma lem1384449 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1384450 : (False = False) = (~ False).
Proof. exact (@lem1384449 False). Qed.
Lemma lem1384452 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1384453 : (False = False) = True.
Proof. exact (TRANS (@lem1384450) (@lem1384452)). Qed.
Lemma lem1384454 (n : nat) (h1 : (real_of_num n) = term1) : ((term3 n) = (term13 n)) = True.
Proof. exact (TRANS (@lem1384447 n h1) (@lem1384453)). Qed.
Lemma lem1384455 (n : nat) (h1 : (real_of_num n) = term1) : True = ((term3 n) = (term13 n)).
Proof. exact (SYM (@lem1384454 n h1)). Qed.
Lemma lem1384456 (n : nat) (h1 : (real_of_num n) = term1) : (term3 n) = (term13 n).
Proof. exact (EQ_MP (@lem1384455 n h1) (@lem0)). Qed.
Lemma lem1384457 (n : nat) : term14 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1384458 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem1384459 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem1384458 n) (@lem1384457 n)). Qed.
Lemma lem1384460 (n : nat) : (term15 n) = ((term15 n) = True).
Proof. exact (@lem7 (term15 n)). Qed.
Lemma lem1384467 (n : nat) : term18 n.
Proof. exact (@lem82 ((real_of_num n) = term1)). Qed.
Lemma lem1384483 (n : nat) (h1 : term3 n) : ((real_of_num n) = term1) = False.
Proof. exact (@lem1384467 n (@lem1384348 n h1)). Qed.
Lemma lem1384484 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384485 (n : nat) (h1 : term3 n) : (term3 n) = (~ False).
Proof. exact (MK_COMB (@lem1384484) (@lem1384483 n h1)). Qed.
Lemma lem1384487 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1384488 (n : nat) (h1 : term3 n) : (term3 n) = True.
Proof. exact (TRANS (@lem1384485 n h1) (@lem1384487)). Qed.
Lemma lem1384489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1384490 (n : nat) (h1 : term3 n) : (term10 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1384489) (@lem1384488 n h1)). Qed.
Lemma lem1384494 (n : nat) : (term15 n) = True.
Proof. exact (EQ_MP (@lem1384460 n) (@lem1384459 n)). Qed.
Lemma lem1384495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384496 (n : nat) : (term12 n) = (and True).
Proof. exact (MK_COMB (@lem1384495) (@lem1384494 n)). Qed.
Lemma lem1384498 (n : nat) (h1 : term3 n) : ((real_of_num n) = term1) = False.
Proof. exact (@lem1384467 n (@lem1384348 n h1)). Qed.
Lemma lem1384499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384500 (n : nat) (h1 : term3 n) : (term3 n) = (~ False).
Proof. exact (MK_COMB (@lem1384499) (@lem1384498 n h1)). Qed.
Lemma lem1384502 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1384503 (n : nat) (h1 : term3 n) : (term3 n) = True.
Proof. exact (TRANS (@lem1384500 n h1) (@lem1384502)). Qed.
Lemma lem1384504 (n : nat) (h1 : term3 n) : (term13 n) = (True /\ True).
Proof. exact (MK_COMB (@lem1384496 n) (@lem1384503 n h1)). Qed.
Lemma lem1384506 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384507 : (True /\ True) = True.
Proof. exact (@lem1384506 True). Qed.
Lemma lem1384508 (n : nat) (h1 : term3 n) : (term13 n) = True.
Proof. exact (TRANS (@lem1384504 n h1) (@lem1384507)). Qed.
Lemma lem1384509 (n : nat) (h1 : term3 n) : ((term3 n) = (term13 n)) = (True = True).
Proof. exact (MK_COMB (@lem1384490 n h1) (@lem1384508 n h1)). Qed.
Lemma lem1384511 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1384512 : (True = True) = True.
Proof. exact (@lem1384511 True). Qed.
Lemma lem1384513 (n : nat) (h1 : term3 n) : ((term3 n) = (term13 n)) = True.
Proof. exact (TRANS (@lem1384509 n h1) (@lem1384512)). Qed.
Lemma lem1384514 (n : nat) (h1 : term3 n) : True = ((term3 n) = (term13 n)).
Proof. exact (SYM (@lem1384513 n h1)). Qed.
Lemma lem1384515 (n : nat) (h1 : term3 n) : (term3 n) = (term13 n).
Proof. exact (EQ_MP (@lem1384514 n h1) (@lem0)). Qed.
Lemma lem1384516 (n : nat) : (term3 n) = (term13 n).
Proof. exact (or_elim (@lem1384346 n) (fun h0 : (real_of_num n) = term1 => @lem1384456 n h0) (fun h0 : term3 n => @lem1384515 n h0)). Qed.
Lemma lem1384517 (n : nat) : (term3 n) = (term9 n).
Proof. exact (EQ_MP (@lem1384385 n) (@lem1384516 n)). Qed.
Lemma lem1384518 (n : nat) : (term3 n) = (term8 n).
Proof. exact (EQ_MP (@lem1384370 n) (@lem1384517 n)). Qed.
Lemma lem1384523 : term19.
Proof. exact (fun n : nat => @lem1384518 n). Qed.
